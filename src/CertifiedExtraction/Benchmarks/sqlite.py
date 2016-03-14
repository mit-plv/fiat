import gc
import random
from time import time
from sys import stderr
from collections import defaultdict

import sqlite3

class TestBench(object):
    def __init__(self):
        self.db = sqlite3.connect(':memory:')
        self.cursor = self.db.cursor()
        self.npids = None
        self.create_table()

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

    def inserts(self, npids):
        self.npids = npids
        rng = random.Random(0) # explicit seed
        records = [(pid, rng.randint(0,1), rng.randint(0, 2**32-1)) for pid in range(npids)]
        for rec in records:
            self.cursor.execute("""INSERT INTO Processes VALUES(?, ?, ?)""", rec)
            self.db.commit()

    def get_cpu_times(self, nqueries):
        rng = random.Random(0)
        pids = [rng.randint(0, self.npids-1) for _ in range(nqueries)]
        for pid in pids:
            self.cursor.execute("""SELECT cputime FROM Processes WHERE pid = ?""", (pid,))
            self.cursor.fetchall()
            self.db.commit()

    def enumerates(self, nqueries):
        rng = random.Random(0)
        states = [rng.randint(0, 1) for _ in range(nqueries)]
        for state in states:
            self.cursor.execute("""SELECT pid FROM Processes WHERE state = ?""", (state,))
            self.cursor.fetchall()
            self.db.commit()

    def with_timer(self, name, f, *args):
        start = time()
        gc.disable()
        try:
            f(*args)
        finally:
            elapsed = time() - start
            results = (name, self.npids, elapsed)
            print("\t".join(str(a) for a in results), file=stderr)
        gc.enable()
        gc.collect()
        return results

def record(results, name, npids, elapsed):
    results[name][npids] = elapsed

def plot(results):
    """Plot a collection of RESULTS.
    RESULTS is a dictionary of {label: list of (x, y)}."""
    from matplotlib import pyplot
    for operation, opresults in results.items():
        xs, ys = zip(*sorted(opresults.items()))
        pyplot.plot(xs, ys, label=operation)
    pyplot.legend()
    pyplot.show()

def read_results(path):
    results = {}
    with open(path):
        for line in path:
            fields = line.strip().split("\t")
            record(results, *fields)
    return results

def benchmark(npids, ngetcputimes, nenumerates):
    results = defaultdict(dict)
    for npid in npids:
        with TestBench() as tb:
            # tb.cursor.execute("""EXPLAIN QUERY PLAN SELECT cputime FROM Processes WHERE pid = 10""")
            # print(list(tb.cursor.fetchall()))
            tb.with_timer("Insert", tb.inserts, npid) #record(results, *)
            record(results, *tb.with_timer("Enumerate", tb.enumerates, ngetcputimes))
            record(results, *tb.with_timer("GetCpuTime", tb.get_cpu_times, nenumerates))
    plot(results)

def main():
    benchmark([n * 10 for n in range(1,100+1)], 1000, 1000)

if __name__ == '__main__':
    main()
