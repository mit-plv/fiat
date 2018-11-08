#!/usr/bin/env python3
"""
Parse and plot the output of microbenchmarks.ml

Because of a bug in Core_bench, this script must deal with prettified output
(requesting raw output crashes Core_bench).  It expects a series of
'│'-separated values, with one input line per test.
"""

import argparse
from collections import OrderedDict
from matplotlib import pyplot, rcParams, patches
import mpl_toolkits.axisartist as axisartist

def parsetime(time):
    if time.endswith("ns"):
        return float(time.replace("_", "")[:-2]) / 1000 # µs
    else:
        raise ValueError(time)

def readline(line):
    line = line.strip()
    fields = (s.strip() for s in line.split("│"))
    _, name, _r2, time, ci, *_ = fields
    ci_low, ci_high = (parsetime(t) for t in ci.split(" "))
    time = parsetime(time)
    return name, time, ci_low, ci_high

def readbench(fname):
    with open(fname) as f:
        return [readline(line) for line in f]

def groupbench(bench):
    grouped = OrderedDict()
    for testname, time, ci_low, ci_high in bench:
        name, direction, proto, kind, size = testname.split("_")
        grouped.setdefault(
            name, OrderedDict()).setdefault(
                direction, OrderedDict()).setdefault(
                    kind, (size, []))[1].append((proto, time, ci_low, ci_high))
    return grouped

HEX = OrderedDict((("yellow", ("#fce94f", "#edd400", "#c4a000")),
                   ("orange", ("#fcaf3e", "#f57900", "#ce5c00")),
                   ("brown",  ("#e9b96e", "#c17d11", "#8f5902")),
                   ("green",  ("#8ae234", "#73d216", "#4e9a06")),
                   ("blue",   ("#729fcf", "#3465a4", "#204a87")),
                   ("purple", ("#ad7fa8", "#75507b", "#5c3566")),
                   ("red",    ("#ef2929", "#cc0000", "#a40000")),
                   ("grey",   ("#eeeeec", "#d3d7cf", "#babdb6")),
                   ("black",  ("#888a85", "#555753", "#2e3436"))))

def plotbench(grouped):
    linum = 0
    colors = OrderedDict([("ether", "orange"),
                          ("arp",   "yellow"),
                          ("ip",    "green"),
                          ("tcp",   "blue"),
                          ("udp",   "purple")])
    labels = OrderedDict([("ether", "Ethernet header"),
                          ("arp",   "ARP header & payload"),
                          ("ip",    "IPv4 header"),
                          ("tcp",   "TCP header & payload"),
                          ("udp",   "UDP header & payload")])

    rcParams.update({
        "font.size": 9,
        "legend.fontsize": 8,
        "font.family": "Fira Mono",
        "axes.titlesize": "medium",
        "xtick.labelsize": "small",
        "ytick.labelsize": "small",
        # "text.usetex": True,
        # "text.latex.unicode": True,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05
    })

    ylabels = []
    fig = pyplot.figure(1, figsize=(4, 3.5))
    fig.subplots_adjust(left=0.5, hspace=0.7)
    ax = axisartist.Subplot(fig, 111)
    fig.add_subplot(ax)

    for name, g in grouped.items():
        ylabels.append(name.upper())
        for direction, g in g.items():
            ylabels.append(" " + direction)
            for kind, (size, measurements) in g.items():
                ylabels.append("  {} ({}b)".format(kind, size))
                offsety = 0
                width = 0.8
                linum = len(ylabels) - 1
                for proto, y, dylow, dyhigh in measurements:
                    color = HEX[colors[proto]]
                    pyplot.barh(-linum - width / 2, [y], width, left=[offsety],
                                color=color[0], edgecolor=color[2], linewidth=0.5, label=proto)
                    offsety += y

    # pyplot.yticks([-n for n in range(len(ylabels))], ylabels)
    ax.set_ylim((-len(ylabels), 0))
    ax.set_xlim((0, 25))
    ax.set_yticks([-n for n in range(len(ylabels))])
    ax.set_yticklabels(ylabels)
    ax.set_xlabel("Single-packet processing time (µs)")
    ax.axis["left"].major_ticklabels.set_ha("left")
    ax.axis["left"].major_ticks.set_visible(False)
    ax.tick_params(axis="y", length=0)
    ax.tick_params(axis=u'both', which=u'both', length=0)

    legend_patches = [patches.Patch(facecolor=HEX[color][0],
                                    edgecolor=HEX[color][2],
                                    label=labels[proto])
                      for proto, color in colors.items()]
    pyplot.legend(handles=legend_patches, loc="upper right", fontsize=8)

    return fig

def parse_arguments():
    parser = argparse.ArgumentParser(description='Plots results of running Core_bench')
    parser.add_argument("fname")
    return parser.parse_args()

def main():
    args = parse_arguments()
    bench = readbench(args.fname)
    grouped = groupbench(bench)
    fig = plotbench(grouped)
    fig.tight_layout()
    pyplot.savefig(args.fname + ".pdf")
    from pprint import pprint
    pprint(grouped)

if __name__ == '__main__':
    main()
