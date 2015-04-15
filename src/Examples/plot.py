import math
from collections import defaultdict
from matplotlib import pyplot, rcParams, ticker
import sys

PHI = (math.sqrt(5) - 1) / 2
PTS_PER_INCH = 72.27

def setParams(width_pt, scale = 2.0):
        width_pt = width_pt * scale
        width_in = width_pt / PTS_PER_INCH
        height_in = width_in / (3 * PHI)

        params = { 'lines.markersize': 5,
                   'lines.linewidth': 1,
                   'axes.labelsize': 12,
                   'xtick.labelsize': 12,
                   'ytick.labelsize': 12,
                   'legend.fontsize': 12,
                   'font.size': 12,
                   'font.family': 'serif',
                   'font.serif': ['Times'],
                   'text.usetex': True,
                   'figure.figsize': (width_in, height_in) }

        rcParams.update(params)

setParams(240)
color = "white"
linestyles = [' ', ' ', ' ', ' ', '-', '-', '-', '-', ':']
markers = ['s', 'o', 's', 'o']
colors = [color, color, color, color, "#3465a4", "#73d216", "#f57900", "#cc0000", "#75507b"]

REFERENCE = 1
INTERESTING = [3, 4, 5, 6]

curves = defaultdict(list)

for line in sys.stdin:
        line = line.strip()
        if line == "":
                continue

        samples = map(float, line.split())
        x = samples[REFERENCE]
        ys = tuple(samples[col] for col in INTERESTING)
        curves[x].append(ys)

fig, axes = pyplot.subplots(1,2)

def merge(group):
        group = tuple(group)
        #print(group)
        return min(group) #sum(group) / len(group)

def tuples_merge(tuples):
        grouped = zip(*tuples)
        return (merge(group) for group in grouped)

x, ys = zip(*sorted(curves.items()))
ys = zip(*map(tuples_merge, ys))

ys = [ys[i] for i in [3,2,1,0]]
ax = [0,0,1,1]
for num, y in enumerate(ys):
        axes[ax[num]].plot(x, y, linestyle=linestyles[num], marker=markers[num], color=colors[num])

axes[0].set_xlabel("Number of books")
axes[1].set_xlabel("Number of books")
axes[0].set_ylabel("Average read time (ms)")
axes[1].set_ylabel("Average write time (ms)")
axes[0].xaxis.set_major_formatter(ticker.FuncFormatter(lambda x, y: '{0:,}'.format(int(x)).replace(',', r'\,')))
axes[0].legend(["NumOrders", "GetTitles"], loc=2, numpoints=1)#, ncol=2)
axes[1].legend(["PlaceOrder", "AddBook"], loc=2, numpoints=1)#, ncol=2)

for ax in axes:
        ax.set_ylim(ymin=0)
        ax.yaxis.set_major_locator(ticker.MaxNLocator(nbins=5, prune='upper'))

pyplot.subplots_adjust(hspace=0.5)
fig.tight_layout(pad=0)

if len(sys.argv) > 1:
        pyplot.savefig(sys.argv[1])
else:
        pyplot.show()
