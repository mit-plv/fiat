#!/usr/bin/env python

from __future__ import with_statement
import fileinput, re

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
    table = []
    table.append('%s | %s | %s' % (col1, col2, col3))
    table.append('%s---%s---%s' % ('-' * len(col1), '-' * len(col2), '-' * len(col3)))
    for line in lines:
        fmatch = FILE_REG.match(line.strip())
        tmatch = TIME_REG.match(line.strip())
        if fmatch:
            (parser, name) = fmatch.groups()
            cur_parser = parser
            if name != cur_file:
                if cur_reference is not None or cur_synthesized is not None:
                    num_chars = cur_file.replace('.', '').rjust(len(col1))
                    cur_reference = ((cur_reference + ' s') if cur_reference is not None else 'None').rjust(len(col2))
                    cur_synthesized = ((cur_synthesized + ' s') if cur_synthesized is not None else 'None').rjust(len(col3))
                    table.append('%s | %s | %s' % (num_chars, cur_reference, cur_synthesized))
                cur_file = name
                cur_reference = None
                cur_synthesized = None
        elif tmatch:
            print('%s (%s): %s' % (cur_parser.ljust(len('reference')), cur_file.replace('.', '').ljust(10), line.strip()))
            (total, median, mean, variance, iterations, per_iteration) = tmatch.groups()
            if per_iteration.rstrip('0') == '1':
                while per_iteration[-1] == '0':
                    if mean[0] == '.': mean = '0' + mean
                    mean_match = re.match(r'^([0-9]*)\.([0-9]*)$', mean)
                    if not mean_match:
                        print('error: %s' % mean)
                        break
                    (pre, post) = mean_match.groups()
                    mean = pre[:-1] + '.' + pre[-1] + post
                    if mean[-1] == '0':
                        mean = mean[:-1]
                    per_iteration = per_iteration[:-1]
                    if mean[0] == '.': mean = '0' + mean
            if cur_parser == 'reference':
                if cur_reference is not None: print('error: %s (%s, %s)' % (cur_parser, cur_reference, mean))
                cur_reference = mean
            elif cur_parser == 'coq':
                if cur_synthesized is not None: print('error: %s (%s, %s)' % (cur_parser, cur_synthesized, mean))
                cur_synthesized = mean
            else:
                print('error: %s' % cur_parser)
    print('\n'.join(table))

if __name__ == '__main__':
    format_output(fileinput.input())
