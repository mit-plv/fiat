#!/usr/bin/python
import sys

class CycleFound (Exception):
    def __init__(self, path, labels):
        self.path = path
        self.labels = labels

    def __str__(self):
        l = len(self.labels)
        result = ""
        for i in range(0, l):
            result = "%s%s %s " % (result, self.path[i], self.labels[i])
        return "%s%s" % (result, self.path[l])

def consistent(lbls, recur=False):
    if len(lbls) == 0:
        return True
    if len(lbls) == 1:
        assert False
    return not (reduce(combine, lbls[1:], lbls[0]) in ['<', '>'])
        
    # if len(lbls) == 2:
    #     return (lbls[0] == '<>') or (combine(lbls[0], symmetric(lbls[1])) <> '<>')
    # else:
    #     return consistent([combine(lbls[0], lbls[1])] + lbls[2:])
    

def combine(old, new, loop=False):
    if old == '<>' or new == '<>':
        return '<>'
    if old == new:
        return old
    if old == '=':
        if new.find('=') <> -1:
            return '='
        return '<>'
    if old == '<':
        if new == '<=' or new == '<':
            return '<'
        return '<>'
    if old == '>':
        if new == '>' or new == '>=':
            return '>'
        return '<>'
    if old == '<=':
        if new.find('=') <> -1:
            return '='
    if old == '>=':
        if new.find('=') <> -1:
            return '='
    
    if loop:
        print old, new
        assert False
    else:
        return combine(new, old, True)

def symmetric(lbl):
    return { '<' : '>'
           , '<=' : '>='
           , '>=' : '<='
           , '>' : '<'
           , '=' : '='
           , '<>' : '<>' }[lbl]

class Graph:
    def __init__(self):
        self._edges = {}
    
    def edge(self, st, en, lbl, loop=False):
        if not self._edges.has_key(st):
            self._edges[st] = {}
        if self._edges[st].has_key(en):
            try:
                x = combine(self._edges[st][en], lbl)
                self._edges[st][en] = x
            except Exception,e:
                raise CycleFound([st, en, st], [lbl, self._edges[st][en]])
        self._edges[st][en] = lbl
        if not loop:
            self.edge(en, st, symmetric(lbl), True)
        
    def edges(self, st):
        if self._edges.has_key(st):
            return self._edges[st]
        return {}

    def nodes(self):
        return self._edges.keys()

    def __str__(self):
        return "%s" % self._edges

    def dump_smt(self, out=sys.stdout):
        def name_of(n):
            return n.replace('.', '_')
        for n in self._edges.keys():
            out.write("(define %s::int)\n" % name_of(n))
        out.write("\n")
        visited = set()
        for (x,es) in self._edges.items():
            for (y, op) in es.items():
                if y in visited:
                    continue
                out.write("(assert (%s %s %s))\n" % (op, name_of(x), name_of(y)))
            visited.add(x)
        out.write("(exit)\n")


def find_cycle(gr):
    visited = set([])
    remaining = set(gr.nodes())   
    
    while len(remaining) > 0:
        root = remaining.pop()
        lvisit = set([root])
        path = []
        labels = []

        def find_strict_cycle(st):
            if st in path:
                f = path.index(st)
                if not consistent(labels[f:]):
                    raise CycleFound(path[f:] + [st], labels[f:])
            if st in visited:
                return None
            
            path.append(st)
            visited.add(st)
            for (to, lbl) in gr.edges(st).items():
                labels.append(lbl)
                find_strict_cycle(to)
                labels.pop()
            path.pop()
                
            return None

        find_strict_cycle(root)
                
    return None

def read_graph(file):
    lines = file.readlines()

    gr = Graph()
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
        gr.edge(st, en, parts[1].strip())

    return gr

def test_combine():
    lbls = ['<', '>', '<=', '>=', '=']
    for x in lbls:
        for y in lbls:
            combine(x,y)

def test_consistent():
    assert not consistent(['>=', '>=', '>'])
    assert consistent(['<', '>'])

if __name__ == '__main__':
    try:
        gr = read_graph(sys.stdin)
        res = find_cycle(gr)
        print "No cycle found"
    except CycleFound,e:
        print "Cycle found!"
        print e
