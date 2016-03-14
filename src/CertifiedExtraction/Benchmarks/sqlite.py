import gc
import random
from time import time
from sys import stderr
from collections import defaultdict, OrderedDict

import numpy
import matplotlib
from matplotlib import pyplot

import sqlite3
import psycopg2

TANGO = OrderedDict((("yellow", ("#fce94f", "#edd400", "#c4a000")),
                     ("orange", ("#fcaf3e", "#f57900", "#ce5c00")),
                     ("brown",  ("#e9b96e", "#c17d11", "#8f5902")),
                     ("green",  ("#8ae234", "#73d216", "#4e9a06")),
                     ("blue",   ("#729fcf", "#3465a4", "#204a87")),
                     ("purple", ("#ad7fa8", "#75507b", "#5c3566")),
                     ("red",    ("#ef2929", "#cc0000", "#a40000")),
                     ("grey",   ("#eeeeec", "#d3d7cf", "#babdb6")),
                     ("black",  ("#888a85", "#555753", "#2e3436"))))

def savitzky_golay(y, window_size, order, deriv=0, rate=1):
    r"""Smooth (and optionally differentiate) data with a Savitzky-Golay filter.
    The Savitzky-Golay filter removes high frequency noise from data.
    It has the advantage of preserving the original shape and
    features of the signal better than other types of filtering
    approaches, such as moving averages techniques.
    Parameters
    ----------
    y : array_like, shape (N,)
        the values of the time history of the signal.
    window_size : int
        the length of the window. Must be an odd integer number.
    order : int
        the order of the polynomial used in the filtering.
        Must be less then `window_size` - 1.
    deriv: int
        the order of the derivative to compute (default = 0 means only smoothing)
    Returns
    -------
    ys : ndarray, shape (N)
        the smoothed signal (or it's n-th derivative).
    Notes
    -----
    The Savitzky-Golay is a type of low-pass filter, particularly
    suited for smoothing noisy data. The main idea behind this
    approach is to make for each point a least-square fit with a
    polynomial of high order over a odd-sized window centered at
    the point.
    Examples
    --------
    t = np.linspace(-4, 4, 500)
    y = np.exp( -t**2 ) + np.random.normal(0, 0.05, t.shape)
    ysg = savitzky_golay(y, window_size=31, order=4)
    import matplotlib.pyplot as plt
    plt.plot(t, y, label='Noisy signal')
    plt.plot(t, np.exp(-t**2), 'k', lw=1.5, label='Original signal')
    plt.plot(t, ysg, 'r', label='Filtered signal')
    plt.legend()
    plt.show()
    References
    ----------
    .. [1] A. Savitzky, M. J. E. Golay, Smoothing and Differentiation of
       Data by Simplified Least Squares Procedures. Analytical
       Chemistry, 1964, 36 (8), pp 1627-1639.
    .. [2] Numerical Recipes 3rd Edition: The Art of Scientific Computing
       W.H. Press, S.A. Teukolsky, W.T. Vetterling, B.P. Flannery
       Cambridge University Press ISBN-13: 9780521880688
    """
    from math import factorial

    try:
        window_size = numpy.abs(numpy.int(window_size))
        order = numpy.abs(numpy.int(order))
    except ValueError:
        raise ValueError("window_size and order have to be of type int")
    if window_size % 2 != 1 or window_size < 1:
        raise TypeError("window_size size must be a positive odd number")
    if window_size < order + 2:
        raise TypeError("window_size is too small for the polynomials order")
    order_range = range(order+1)
    half_window = (window_size -1) // 2
    # precompute coefficients
    b = numpy.mat([[k**i for i in order_range] for k in range(-half_window, half_window+1)])
    m = numpy.linalg.pinv(b).A[deriv] * rate**deriv * factorial(deriv)
    # pad the signal at the extremes with
    # values taken from the signal itself
    firstvals = y[0] - numpy.abs( y[1:half_window+1][::-1] - y[0] )
    lastvals = y[-1] + numpy.abs(y[-half_window-1:-1][::-1] - y[-1])
    y = numpy.concatenate((firstvals, y, lastvals))
    return numpy.convolve( m[::-1], y, mode='valid')

class TestBench(object):
    def __init__(self):
        self.db = self.connect()
        self.cursor = self.db.cursor()
        self.npids = None
        self.create_table()

    def connect(self):
        raise NotImplementedError()

    def parametrize(self, query):
        raise NotImplementedError()

    def execute(self, query, *args):
        query = self.parametrize(query)
        self.cursor.execute(query, *args)

    def __enter__(self):
        return self

    def __exit__(self, *ignored):
        self.cursor.close()

    def create_table(self):
        self.cursor.execute("""DROP TABLE IF EXISTS Processes""")
        self.cursor.execute("""CREATE TABLE Processes
                             (pid INTEGER NOT NULL, state INTEGER NOT NULL, cputime INTEGER NOT NULL)""")
        self.cursor.execute("""CREATE UNIQUE INDEX pid_idx ON Processes (state, pid)""")
        self.db.commit()

    def spawns(self, npids):
        self.npids = npids
        rng = random.Random(0) # explicit seed
        records = [(pid, rng.randint(0,1), rng.randint(0, 2**15-1)) for pid in range(npids)]
        for rec in records:
            self.execute("""INSERT INTO Processes VALUES(__, __, __)""", rec)
            self.db.commit()

    def get_cpu_times(self, nqueries):
        rng = random.Random(0)
        for _ in range(nqueries):
            pid = rng.randint(0, self.npids-1)
            self.execute("""SELECT cputime FROM Processes WHERE pid = __""", (pid,))
            self.cursor.fetchall()
            self.db.commit()

    def enumerates(self, nqueries):
        rng = random.Random(0)
        for _ in range(nqueries):
            state = rng.randint(0, 1)
            self.execute("""SELECT pid FROM Processes WHERE state = __""", (state,))
            self.cursor.fetchall()
            self.db.commit()

    def with_timer(self, name, f, *args):
        start = time()
        gc.disable()
        try:
            f(*args)
        finally:
            elapsed = time() - start
            results = (name, self.npids, elapsed) + args
            print("\t".join(str(a) for a in results), file=stderr)
        gc.enable()
        gc.collect()
        return results

class SQLiteTestBench(TestBench):
    def connect(self):
        return sqlite3.connect(':memory:')

    def parametrize(self, query):
        return query.replace("__", "?")

class PostgreTestBench(TestBench):
    def connect(self):
        return psycopg2.connect('dbname=fiat-to-facade user=clement')

    def parametrize(self, query):
        return query.replace("__", "%s")

def record(results, name, npids, *data):
    results[name][int(npids)] = [float(data[0])] + [int(d) for d in data[1:]]

def read_results(path):
    results = defaultdict(dict)
    with open(path) as infile:
        for line in infile:
            fields = line.strip().split("\t")
            record(results, *fields)
    return results

def write_results(path, results):
    with open(path, mode="w") as outfile:
        for name in results:
            curve = results[name]
            for npids in curve:
                outfile.write("\t".join(map(str, [name, npids] + curve[npids])) + "\n")

def benchmark(prefix, bench, npids, ngetcputimes, nenumerates):
    results = defaultdict(dict)
    for npid in npids:
        with bench() as tb:
            # tb.cursor.execute("""EXPLAIN QUERY PLAN SELECT cputime FROM Processes WHERE pid = 10""")
            # print(list(tb.cursor.fetchall()))
            record(results, *tb.with_timer(prefix + "Spawn", tb.spawns, npid))
            record(results, *tb.with_timer(prefix + "Enumerate", tb.enumerates, ngetcputimes))
            record(results, *tb.with_timer(prefix + "GetCpuTime", tb.get_cpu_times, nenumerates))
    return results

def plot_set(axis, results, color, markers):
    """Plot a collection of RESULTS on AXIS.
    RESULTS is a dictionary of {label: list of (x, (y :: junk))}."""
    legend = []
    for (opname, opresults), marker in zip(sorted(results.items()), markers):
        if "Spawn" not in opname:
            xs, data = zip(*sorted(opresults.items()))
            ys = numpy.array([rec[0] for rec in data])
            line, = axis.plot(xs, savitzky_golay(ys, 19, 3), color=color, linestyle="-", marker="")
            dots, = axis.plot(xs, ys, color=color, linestyle="", marker=marker)
            legend.append(((line, dots), opname))
    return legend

def to_inches(points):
    return points / 72.26999

def rcparams():
    matplotlib.rcParams.update({
        "font.size": 9,
        "font.family": "serif",
        "font.serif": "times",
        "axes.titlesize": "medium",
        "xtick.labelsize": "small",
        "ytick.labelsize": "small",
        "legend.fontsize": "medium",
        "text.usetex": True,
        "text.latex.unicode": True,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05
    })

def plot(*result_sets):
    rcparams()
    fig = pyplot.figure(figsize=(to_inches(504.0),)*2)
    axis = fig.add_subplot(1,1,1)
    legend = []
    for results, color in zip(result_sets, ("orange", "green", "purple")):
        legend.extend(plot_set(axis, results, color, (".", "x")))
    axis.set_yscale('log')
    axis.legend(*zip(*legend))
    fig.show()

def main():
    npids = [n*10 for n in range(1,100+1)]
    nenumerates = 10000
    ngetcputimes = 10000

    # results = benchmark("Postgre/", PostgreTestBench, npids, nenumerates, ngetcputimes)
    # write_results("postgre.out", results)

    # results = benchmark("SQLite/", SQLiteTestBench, npids, nenumerates, ngetcputimes)
    # write_results("sqlite.out", results)

    plot(read_results("postgre.out"), read_results("sqlite.out"))

if __name__ == '__main__':
    main()
