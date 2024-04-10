import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
import statsmodels.api as sm
import matplotlib.ticker as tk
from matplotlib import rc

rc('font', family='Libertine', size=15)
rc('text', usetex=True)
rc('text.latex', preamble=r'\usepackage{libertine}\usepackage{newtxmath}')

origin = np.genfromtxt("timing.csv", delimiter=",")

pseudocount = 1
reasoning = origin[:,0] / 1000.0 # they are in unit of microseconds
proof_eval = origin[:,1] / 1000.0
proof_search = origin[:,2]
total = origin[:,3]

print(proof_search.size)

proof_eval = proof_eval[proof_eval > 0]
proof_search = proof_search[proof_search > 0]

print(proof_search.size)

log_reasoning = np.log10(np.maximum(reasoning, 10.0) + pseudocount) 
log_proof_eval = np.log10(np.maximum(proof_eval, 10.0) + pseudocount)
log_proof_search = np.log10(np.minimum(np.maximum(proof_search, 10.0), 3000000.0) + pseudocount)
log_total = np.log10(total + pseudocount)

tick_values = [10.0, 30.0, 100.0, 300.0, 1000.0, 3000.0, 10000.0, 30000.0, 100000.0, 300000.0, 1000000]
tick_names  = ['$\leq 0.01$', '', '0.1', '0.3', '1', '3', '10', '', '', '100 seconds', '']
log_lower = np.log10(pseudocount + 10.0)
log_upper = np.log10(pseudocount + 1000000.0)


def normalize_histogram(hist, bin_edges):
    return hist / sum(hist) * 100.0

log_hist1, log_bin_edges1 = np.histogram(log_reasoning, bins=30, range=(log_lower, log_upper))
log_hist2, log_bin_edges2 = np.histogram(log_proof_eval, bins=30, range=(log_lower, log_upper))
log_hist3, log_bin_edges3 = np.histogram(log_proof_search, bins=30, range=(log_lower, log_upper))
log_hist4, log_bin_edges4 = np.histogram(log_total, bins=30, range=(log_lower, log_upper))

log_hist1 = normalize_histogram (log_hist1, log_bin_edges1)
log_hist2 = normalize_histogram (log_hist2, log_bin_edges2)
log_hist3 = normalize_histogram (log_hist3, log_bin_edges3)
log_hist4 = normalize_histogram (log_hist4, log_bin_edges4)

plt.figure(figsize=(4.3, 2.8))

def plot_hist_as_line(hist, bin_edges, label, linestyle, color):
    bin_centers = 0.5 * (bin_edges[1:] + bin_edges[:-1])
    plt.plot(bin_centers, hist, label=label, color=color, linestyle=linestyle)

plot_hist_as_line(log_hist1, log_bin_edges1, 'reasoning', '--', '#6B6B07')
plot_hist_as_line(log_hist2, log_bin_edges2, 'proof eval', ':', '#073A5E')
plot_hist_as_line(log_hist3, log_bin_edges3, 'proof search', '-.', '#610807')
plot_hist_as_line(log_hist4, log_bin_edges4, 'total', '-', 'black')


log_tick_positions = [np.log10(tick + pseudocount) for tick in tick_values]
plt.xticks(log_tick_positions, tick_names)


plt.yticks([0,5,10,15,20])

ax = plt.gca()
ax.yaxis.set_major_formatter(tk.PercentFormatter(decimals=0))
ax.xaxis.set_label_coords(0.955, -0.025)
ax.xaxis.label.set_bbox(dict(facecolor='white', edgecolor='none', pad=3))
ax.xaxis.get_majorticklabels()[2].set_horizontalalignment("right")

plt.legend(framealpha=0.75, labelspacing=0.2, loc='upper center')

plt.grid(linestyle=':')

plt.show()

