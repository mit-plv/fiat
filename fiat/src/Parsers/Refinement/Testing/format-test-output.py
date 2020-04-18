#!/usr/bin/env python

from __future__ import with_statement
import fileinput, re, sys

def make_table_line(cur_reference, cur_synthesized, cur_file, col1, col2, col3, col4):
    num_chars = cur_file.replace('.', '').rjust(len(col1))
    if cur_reference is not None and cur_synthesized is not None and cur_reference.strip('.0') != '':
        ratio = str(float(cur_synthesized) / float(cur_reference) * 100)
    else:
        ratio = None
    cur_reference = ((cur_reference + ' s') if cur_reference is not None else 'None').rjust(len(col2))
    cur_synthesized = ((cur_synthesized + ' s') if cur_synthesized is not None else 'None').rjust(len(col3))
    ratio = ((ratio + ' % slower') if ratio is not None else 'N/A').rjust(len(col4))
    return '%s | %s | %s | %s' % (num_chars, cur_reference, cur_synthesized, ratio)


def format_output(lines):
    FILE_REG = re.compile(r'^(reference|coq)\s*ab(1[0\.]*)$')
    TIME_REG = re.compile(r'^total: ([0-9\.]*), median: ([0-9\.]*), mean: ([0-9\.]*), sample variance: ([0-9\.]*), iterations: ([0-9]*) \(([0-9]*) on each\)$')
    cur_file = None
    cur_parser = None
    cur_reference = None
    cur_synthesized = None
    col1 = '# characters'
    col2 = 'hand-written'
    col3 = 'synthesized'
    col4 = 'ratio'
    table = []
    table.append('%s | %s | %s | %s' % (col1, col2, col3, col4))
    table.append('%s---%s---%s---%s' % tuple('-' * len(i) for i in (col1, col2, col3, col4)))
    for line in lines:
        fmatch = FILE_REG.match(line.strip())
        tmatch = TIME_REG.match(line.strip())
        if fmatch:
            (parser, name) = fmatch.groups()
            cur_parser = parser
            if name != cur_file:
                if cur_reference is not None or cur_synthesized is not None:
                    table.append(make_table_line(cur_reference, cur_synthesized, cur_file, col1, col2, col3, col4))
                cur_file = name
                cur_reference = None
                cur_synthesized = None
        elif tmatch:
            print('%s (%s): %s' % (cur_parser.ljust(len('reference')), cur_file.replace('.', '').ljust(10), line.strip()))
            sys.stdout.flush()
            (total, median, mean, variance, iterations, per_iteration) = tmatch.groups()
            time_displayed = median
            if per_iteration.rstrip('0') == '1':
                while per_iteration[-1] == '0':
                    if time_displayed[0] == '.': time_displayed = '0' + time_displayed
                    time_displayed_match = re.match(r'^([0-9]*)\.([0-9]*)$', time_displayed)
                    if not time_displayed_match:
                        print('error: %s' % time_displayed)
                        break
                    (pre, post) = time_displayed_match.groups()
                    time_displayed = pre[:-1] + '.' + pre[-1] + post
                    if time_displayed[-1] == '0':
                        time_displayed = time_displayed[:-1]
                    per_iteration = per_iteration[:-1]
                    if time_displayed[0] == '.': time_displayed = '0' + time_displayed
            if cur_parser == 'reference':
                if cur_reference is not None: print('error: %s (%s, %s)' % (cur_parser, cur_reference, time_displayed))
                cur_reference = time_displayed
            elif cur_parser == 'coq':
                if cur_synthesized is not None: print('error: %s (%s, %s)' % (cur_parser, cur_synthesized, time_displayed))
                cur_synthesized = time_displayed
            else:
                print('error: %s' % cur_parser)
    if cur_reference is not None or cur_synthesized is not None:
        table.append(make_table_line(cur_reference, cur_synthesized, cur_file, col1, col2, col3, col4))
    print('\n'.join(table))

if __name__ == '__main__':
    format_output(fileinput.input())
