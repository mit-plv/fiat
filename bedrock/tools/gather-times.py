#!/usr/bin/python

import re
import sys
import prettytable

LINE_PTRN = re.compile(r'([^\s]+):\s*\(total:([0-9\.]+),\s*mean:([0-9\.]+),\s*runs:([0-9]+),\s*sigma2:([0-9\.]+)\)')
CMD_PTRN = re.compile(r'time coqc.*\s([A-Za-z]+)$')
SUMM_PTRN = re.compile(r'([0-9:\.]+)user\s+([0-9:\.]+)system\s+([0-9:\.]+)elapsed')

def parse_file_data(stream):
    """returns the file data"""
    data = {}

    for i in stream:
        if i == "":
            break
        m = LINE_PTRN.match(i)
        if not m is None:
            data[m.group(1)] = { 'total' : float(m.group(2))
                               , 'mean'  : float(m.group(3))
                               , 'runs'  : int(m.group(4))
                               , 'sigma' : float(m.group(5))
                               }
        
    return data

def parse_files(stream):
    data = {}
    last = None

    for i in stream:
        m = CMD_PTRN.match(i)
        if not m is None:
            data[m.group(1)] = parse_file_data(stream)
            last = m.group(1)
        else:
            m = SUMM_PTRN.match(i)
            if not last is None and not m is None:
                data[last]['SUMMARY'] = { 'elapsed' : m.group(3) }
            else:
                pass

    return data

def phase_summary(data):
    # get the keys
    all_keys = reduce(lambda x,y: x.union(y),
                      [set(x.keys()) for x in data.values()],
                      set([]))
    all_keys = all_keys - set(['SUMMARY'])

    # init the accumulator
    acc = {}
    for x in all_keys:
        acc[x] = { 'total' : 0.0 , 'runs' : 0 }

    # accumulate
    for (_,d) in data.items():
        for k in [x for x in d.keys() if not x == 'SUMMARY']:
            acc[k] = { 'total' : acc[k]['total'] + d[k]['total']
                     , 'runs' : acc[k]['runs'] + d[k]['runs']
                     }

    return acc

def print_phase_summary(summary):
    sorted_keys = summary.keys()
    sorted_keys.sort()
    
    # print the accumulator
    tbl = prettytable.PrettyTable(["Phase", "Total (s)", "Runs"])
    tbl.set_style(prettytable.PLAIN_COLUMNS)
    tbl.align["Phase"] = "l"
    tbl.align["Total (s)"] = "r"
    tbl.align["Runs"]  = "r"
    
    for k in sorted_keys:
        tbl.add_row([k, summary[k]['total'], summary[k]['runs']])

    print tbl

def print_file_data(data):
    for (f, d) in data.items():
        print ""
        if 'SUMMARY' in d:
            print "%s (elapsed: %s)" % (f, d['SUMMARY']['elapsed'])
        else:
            print f
        tbl = prettytable.PrettyTable(["Phase", "Total (s)", "Mean (s)", "Runs", "Sigma (s)"])
        tbl.set_style(prettytable.PLAIN_COLUMNS)
        tbl.align["Phase"] = "l"
        tbl.align["Total (s)"] = "r"
        tbl.align["Mean (s)"] = "r"
        tbl.align["Runs"]  = "r"
        tbl.align["Sigma (s)"]  = "r"        
        tbl.sortby = "Phase"
        for (ph,da) in d.items():
            if not ph == 'SUMMARY':
                tbl.add_row([ph, da['total'], da['mean'], da['runs'], da['sigma']])
        print tbl
    

def reader(files):
    for f in files:
        f = open(f, 'r')
        for x in f.readlines():
            yield x.strip()
    yield ""

def main():
    f = sys.argv[1]
    res = parse_files(reader(sys.argv[1:]))

    summary = phase_summary(res)
    
    print_phase_summary(summary)

    print_file_data(res)
    
    return 0

if __name__ == '__main__':
    sys.exit(main())
    
