#!/usr/bin/env python3
"""Parse and plot the output of microbenchmarks.ml."""

import argparse
from collections import OrderedDict

from matplotlib import pyplot, rcParams, patches
import mpl_toolkits.axisartist as axisartist
import matplotlib.ticker as plticker
import sexpdata

def read_experiment(b):
    b = dict(b)
    name = b['benchmark_name_with_index']
    time = b['time_per_run_nanos'] / 1000 # µs
    ci_low = b['ci95_lower_bound']
    ci_high = b['ci95_upper_bound']
    return name, time, ci_low, ci_high

def remove_symbols(sexp):
    if isinstance(sexp, sexpdata.SExpBase):
        return sexp.value()
    if isinstance(sexp, (int, float, str)):
        return sexp
    assert isinstance(sexp, list)
    return [remove_symbols(s) for s in sexp]

def readbench(fname):
    with open(fname) as f:
        sexp_str = next(l for l in f if l.startswith('('))
        sexp_experiments = remove_symbols(sexpdata.loads(sexp_str, nil=None, true=None, false=None))
        return [read_experiment(b) for b in sexp_experiments]

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
    # labels = OrderedDict([("ether", "Ethernet header"),
    #                       ("arp",   "ARP header & payload"),
    #                       ("ip",    "IPv4 header"),
    #                       ("tcp",   "TCP header & payload"),
    #                       ("udp",   "UDP header & payload")])
    labels = OrderedDict([("ether", "Ethernet"),
                          ("arp",   "ARP"),
                          ("ip",    "IPv4"),
                          ("tcp",   "TCP"),
                          ("udp",   "UDP")])

    rcParams.update({
        "font.size": 9,
        "legend.fontsize": 8,
        "font.family": "Ubuntu Mono",
        "axes.titlesize": "medium",
        "xtick.labelsize": "small",
        "ytick.labelsize": "small",
        # "text.usetex": True,
        # "text.latex.unicode": True,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05
    })

    ylabels = []
    fig = pyplot.figure(1, figsize=(4, 2.75))
    fig.subplots_adjust(left=0.5, hspace=0.7)
    ax = axisartist.Subplot(fig, 111)
    fig.add_subplot(ax)

    THICKNESS = 1
    LINE_HEIGHT = THICKNESS * 1.3
    for name, g in grouped.items():
        # ylabels.append(name.upper())
        for direction, g in g.items():
            size = list(set(size for (_, (size, _)) in g.items()))[0]
            ylabels.append("{} {}".format(name.upper(), direction)) #  ({}b)
            # name = " " * len(name) # Omit names on next iterations
            for kind, (sz, measurements) in g.items():
                assert sz == size
                ylabels.append("  {} ({}b)".format(kind, sz))
                width_acc = 0
                linum = (len(ylabels) - 1) * LINE_HEIGHT
                for proto, width, dwlow, dwhigh in measurements:
                    # print(width, dwlow, dwhigh)
                    color = HEX[colors[proto]]
                    bottom = -linum
                    pyplot.errorbar([width_acc + width], [bottom], # xerr=[[-dwlow], [dwhigh]],
                                    ecolor=color[2], fmt='')
                    pyplot.barh(bottom, [width], THICKNESS, left=[width_acc],
                                color=color[0], edgecolor=color[2], linewidth=0.5, label=proto)
                    width_acc += width

    ax.set_ylim((-len(ylabels) * LINE_HEIGHT, 0))
    # ax.set_xlim((0, 4.75))
    ax.set_yticks([-n * LINE_HEIGHT for n in range(len(ylabels))])
    ax.set_yticklabels(ylabels)
    ax.set_xlabel("Single-packet processing time (µs)")
    # ax.set_xticks([x * 0.5 for x in range(5 * 2)])
    ax.axis["left"].major_ticklabels.set_ha("left")
    ax.axis["left"].major_ticks.set_visible(False)
    ax.axis["top"].major_ticks.set_visible(False)
    ax.axis["right"].major_ticks.set_visible(False)
    ax.axis["bottom"].major_ticks.set_ticksize(2)

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
    pdf_path = args.fname + ".pdf"
    pyplot.savefig(pdf_path)
    print("Figure written to {}".format(pdf_path))
    # from pprint import pprint
    # pprint(grouped)

if __name__ == '__main__':
    main()
