#!/usr/bin/python
import sys

def read_constraints(file):
    lines = file.readlines()

    nodes = set()
    edges = set()

    last = None
    for ln in lines:
        ln = ln.replace(';', '')
        parts = ln.split()
        if len(parts) == 3:
            last = parts[0]
        elif len(parts) == 2:
            parts = [last, parts[0], parts[1]]
        else:
            assert False
            
        st = parts[0].strip()
        en = parts[2].strip()
        nodes.add(st)
        nodes.add(en)
        edges.add((st,en,parts[1].strip()))

    return (nodes, edges)

def dump_smt(nodes, edges, out=sys.stdout):
    def name_of(n):
        return n.replace('.', '_')

    for n in nodes:
        out.write("(define %s::int)\n" % name_of(n))
    out.write("\n")
    for (st, en, op) in edges:
        out.write("(assert (%s %s %s))\n" % (op, name_of(st), name_of(en)))
        
    out.write("(exit)\n")

if __name__ == '__main__':
    (nodes, edges) = read_constraints(sys.stdin)

    dump_smt(nodes, edges)
