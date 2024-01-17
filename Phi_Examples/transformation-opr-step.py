import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
import pandas as pd
import statsmodels.formula.api as smf
from matplotlib.ticker import MaxNLocator


from matplotlib import rc

# Set up for using the desired fonts
rc('font', family='Libertine', size=15)
rc('text', usetex=True)
rc('text.latex', preamble=r'\usepackage{libertine}\usepackage{newtxmath}')


origin = np.genfromtxt("transformation-opr-step.csv", delimiter=",")
X = origin[:,0]
Y = origin[:,1]
data = pd.DataFrame({'X': X, 'Y': Y})
#data['X2'] = data['X']**2

#quantile_model_quad = smf.quantreg('Y ~ X + X2', data).fit(q=0.95)
quantile_model_quad = smf.quantreg('Y ~ X', data).fit(q=0.95)
summary_quad = quantile_model_quad.summary()


x_range = np.linspace(X.min(), X.max(), 100)
#y_fit = quantile_model_quad.params['Intercept'] + quantile_model_quad.params['X'] * x_range + quantile_model_quad.params['X2'] * x_range**2
y_fit = quantile_model_quad.params['Intercept'] + quantile_model_quad.params['X'] * x_range #+ quantile_model_quad.params['X2'] * x_range**2

plt.figure(figsize=(4.3, 2.9))
plt.plot(x_range, y_fit, linestyle='--', linewidth=0.6, color='black', label=r'\parbox{7em}{95th percentile\\regression}')

#plt.title('Scatter plot with high transparency')
plt.scatter(X, Y, color='grey', alpha=0.2, edgecolors='none')
plt.xlabel("100 typ oprs")
#plt.ylabel("LP steps")
#ax.xaxis.set_label_coords(0.85, -0.045)
#ax.xaxis.label.set_bbox(dict(facecolor='white', edgecolor='none', pad=3))
#ax.xaxis.set_major_locator(MaxNLocator(nbins='auto'))
plt.xticks([0,25,50,75,100], ['0','25','50','75', '100 typ oprs'])
ax = plt.gca()  # Get the current axis
ax.xaxis.get_majorticklabels()[3].set_horizontalalignment("right")
plt.yticks([50,100,150,200,250])

plt.legend(framealpha=0.1)
#plt.tight_layout()
plt.show()


