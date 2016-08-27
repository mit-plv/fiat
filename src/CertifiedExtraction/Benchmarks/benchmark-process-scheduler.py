#!/usr/bin/env python3
import gc
import random
import sys
import re
from time import time
from sys import stderr
from argparse import ArgumentParser
from collections import defaultdict, OrderedDict

import numpy
import matplotlib
from matplotlib import pyplot
import matplotlib.patches as mpatches

import sqlite3
import psycopg2
import pymysql

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
        # print(query)
        self.cursor.execute(query, *args)

    def __enter__(self):
        return self

    def __exit__(self, *ignored):
        self.cursor.close()

    def create_table(self):
        self.cursor.execute("""DROP TABLE IF EXISTS Processes""")
        self.cursor.execute("""CREATE TABLE Processes
                             (pid INTEGER NOT NULL, state INTEGER NOT NULL, cputime INTEGER NOT NULL)""")
        self.cursor.execute("""CREATE INDEX pid_idx ON Processes (state, pid)""")
        self.db.commit()

    def spawns(self, npids):
        self.npids = npids
        rng = random.Random(0) # explicit seed
        pids = rng.shuffle(list(range(npids)))
        for pid in pids:
            rec = (pid, int(pid % (1 + npids // 10) == 0), rng.randint(0, 2**15-1))
            self.execute("""INSERT INTO Processes VALUES(__, __, __)""", rec)
        self.db.commit()

    def get_cpu_times(self, nqueries):
        rng = random.Random(0)
        for _ in range(nqueries):
            pid = rng.randint(0, self.npids-1)
            self.execute("""SELECT cputime FROM Processes WHERE pid = __""", (pid,))
            self.cursor.fetchall()
        self.db.commit()

    def get_cpu_times_with_extra_clause(self, nqueries):
        rng = random.Random(0)
        for _ in range(nqueries):
            pid = rng.randint(0, self.npids-1)
            self.execute("""SELECT cputime FROM Processes WHERE state IN (0, 1) AND pid = __""", (pid,))
            self.cursor.fetchall()
        self.db.commit()

    def enumerates(self, nqueries):
        # rng = random.Random(0)
        for _ in range(nqueries):
            # state = rng.randint(0, 1)
            self.execute("""SELECT pid FROM Processes WHERE state = 1""")
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
        return psycopg2.connect('dbname=fiat-to-facade')

    def parametrize(self, query):
        return query.replace("__", "%s")

class MySQLTestBench(TestBench):
    """
    CREATE USER 'fiat'@'localhost' IDENTIFIED BY 'fiat';
    GRANT ALL PRIVILEGES ON * . * TO 'fiat'@'localhost';
    FLUSH PRIVILEGES;
    CREATE DATABASE fiat_to_facade;
    """

    def connect(self):
        return pymysql.connect(host="localhost", user="fiat", passwd="fiat", db="fiat_to_facade")

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

def benchmark(prefix, bench, npids, nenumerates, ngetcputimes):
    results = defaultdict(dict)
    for npid in npids:
        with bench() as tb:
            # tb.cursor.execute("""EXPLAIN SELECT cputime FROM Processes WHERE pid = 10""")
            # print(list(tb.cursor.fetchall()))
            record(results, *tb.with_timer(prefix + "Spawn", tb.spawns, npid))
            record(results, *tb.with_timer(prefix + "Enumerate", tb.enumerates, nenumerates))
            record(results, *tb.with_timer(prefix + "GetCPUTime", tb.get_cpu_times, ngetcputimes))
            record(results, *tb.with_timer(prefix + "GetCPUTime'", tb.get_cpu_times_with_extra_clause, nenumerates))
    return results

def out_file_name(prefix, nenumerates, ngetcputimes):
    return "{}-{}-{}.out".format(prefix, nenumerates, ngetcputimes)

def benchmark_helper(prefix, bench, npids, nenumerates, ngetcputimes):
    results = benchmark(prefix + "/", bench, npids, nenumerates, ngetcputimes)
    write_results(out_file_name(prefix, nenumerates, ngetcputimes), results)

def relabel_curve(name):
    for rep_pair in [("Postgre", "PG"), ("Cpu", "CPU"), ("GetCPUTime", "CPU"), ("Enumerate", "Enum")]:
        name = name.replace(*rep_pair)
    return name

def order_curves(curve):
    return ["Enum", "CPU'", "CPU"].index(re.sub(".*/", "", curve[0]))

def cleanup_curves(curves):
    return [(relabel_curve(name), curve) for (name, curve) in curves.items()
       if ("Spawn" not in name and "Explicit" not in name)]

def plot_set(axes, results, linestyle, markers, colors):
    """Plot a collection of RESULTS on AXIS.
    RESULTS is a dictionary of {label: list of (x, (y :: junk))}."""
    legend = []
    results = sorted(cleanup_curves(results), key=order_curves)
    for (opname, opresults), axis, marker, color in zip(results, axes, markers, colors):
        print("Plotting {} in {}".format(opname, color))
        xs, data = zip(*sorted((k, v) for (k, v) in opresults.items() if 20 <= k <= 5000))
        ys = numpy.array([rec[0] for rec in data])
        smoothing = (len(ys) // 30) * 2 + 3
        line, = axis.plot(xs, savitzky_golay(ys, smoothing, 3), #dash_capstyle="round",
                          color=color, linestyle=linestyle, marker="", linewidth=2, zorder=3)
        dots, = axis.plot(xs, ys, linestyle="",
                          marker="", markevery=15, markerfacecolor="none",
                          markeredgewidth=0.5, markeredgecolor=color,  markersize=5)
        legend.append(((mpatches.Patch(facecolor='none', edgecolor=TANGO["grey"][2], linewidth=0.3), line, dots),
                       "{{\\fontsize{{9}}{{1}}\\selectfont{{}}{}\\fontsize{{8}}{{1}}\\selectfont{{}}\\textsf{{/{}}}}}".format(*opname.split("/"))))
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
        "legend.fontsize": 8,
        "text.usetex": True,
        "text.latex.unicode": True,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05
    })

def plot_sets(*result_sets):
    rcparams()

    figsize = [d * to_inches(240.0) for d in (1, 0.8)]
    fig, axis = pyplot.subplots(1, 1, sharex=True, frameon=False, figsize=figsize)
    axis.grid(which='minor', color=TANGO["grey"][1], zorder=0)
    axis.grid(which='major', color=TANGO["black"][2], zorder=0)
    axis.set_yscale('log', basey=10)
    axis.set_ylim((0.4e-2, 5))

    legends = []
    colors = [TANGO[color][0] for color in ("purple", "orange", "red")]
    linestyles = ((0, (1, 1)), (0, (8, 8)), "-")
    for results, linestyle in zip(result_sets, linestyles):
        set_legend = plot_set((axis,)*len(results), results, linestyle, ("+", "x", "o"), colors)
        if len(set_legend) < 3:
            set_legend.append((mpatches.Patch(color='none'), ""))
        legends.extend(reversed(set_legend))

    axis.legend(*zip(*legends), loc='lower center', frameon=False,
                columnspacing=1.2, handletextpad=0.4, handlelength=2.5,
                bbox_to_anchor=(0.5,-0.42), ncol=3, numpoints=2).get_frame().set_linewidth(0.5)
    axis.set_xlabel("Number of processes ($10$ active, $n-10$ sleeping)")
    axis.set_ylabel("Running time (seconds)")

    # pyplot.show()
    fig.savefig("../../../../papers/fiat-to-facade/benchmarks.pdf")

def compute_npids(maxpid):
    return [n*10 for n in range(1,maxpid//10+1)]

def benchmark_bedrock(args):
    import subprocess
    with open(out_file_name("Bedrock", args.nenumerates, args.ngetcputimes), mode="wb") as outfile:
        for pid in args.npids:
            bedrock_args = [args.exec] + [str(arg) for arg in (pid, args.nenumerates, args.ngetcputimes)]
            output = subprocess.check_output(bedrock_args)
            print(output.decode('ascii'))
            outfile.write(subprocess.check_output(bedrock_args))

def benchmark_rdbms(args):
    benchmark_helper("Postgre", PostgreTestBench, args.npids, args.nenumerates, args.ngetcputimes)
    benchmark_helper("SQLite", SQLiteTestBench, args.npids, args.nenumerates, args.ngetcputimes)
    # benchmark_helper("MySQL", MySQLTestBench, npids, nenumerates, ngetcputimes)

def plot(args):
    #read_results(out_file_name("MySQL", nenumerates, ngetcputimes)),
    plot_sets(read_results(out_file_name("Postgre", args.nenumerates, args.ngetcputimes)),
              read_results(out_file_name("SQLite", args.nenumerates, args.ngetcputimes)),
              read_results(out_file_name("Bedrock", args.nenumerates, args.ngetcputimes)))

def parse_args():
    parser = ArgumentParser(description='Benchmark databases.')
    parser.add_argument("--max_npids", default=5000)
    parser.add_argument("--nenumerates", default=20000)
    parser.add_argument("--ngetcputimes", default=10000)

    subparsers = parser.add_subparsers(help='Action', dest="action")
    subparsers.required = True

    rdbms_parser = subparsers.add_parser("rdbms", help="Benchmark PostgreSQL, SQLite, and MySQL.")
    rdbms_parser.set_defaults(callback=benchmark_rdbms)

    bedrock_parser = subparsers.add_parser("bedrock", help="Benchmark Bedrock.")
    bedrock_parser.add_argument("exec", help="Path to the Bedrock executable")
    bedrock_parser.set_defaults(callback=benchmark_bedrock)

    plot_parser = subparsers.add_parser("plot", help="Plot results.")
    plot_parser.set_defaults(callback=plot)

    args = parser.parse_args(sys.argv[1:] if len(sys.argv) >= 1 else ["plot"])
    args.npids = compute_npids(args.max_npids)

    return args

def main():
    args = parse_args()
    args.callback(args)

if __name__ == '__main__':
    main()
