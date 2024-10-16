import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
import pandas as pd
import statsmodels.formula.api as smf
from matplotlib.ticker import MaxNLocator
from matplotlib import rc

rc('font', family='Libertine', size=16)
rc('text', usetex=True)
rc('text.latex', preamble=r'\usepackage{libertine}\usepackage{newtxmath}')


origin = np.genfromtxt("transformation-opr-step.csv", delimiter=",")
X = origin[:,0]
Y = origin[:,1]
data = pd.DataFrame({'X': X, 'Y': Y})

quantile_model_quad = smf.quantreg('Y ~ X', data).fit(q=0.95)
summary_quad = quantile_model_quad.summary()


x_range = np.linspace(X.min(), X.max(), 100)
y_fit = quantile_model_quad.params['Intercept'] + quantile_model_quad.params['X'] * x_range

plt.figure(figsize=(4, 4))
plt.plot(x_range, y_fit, linestyle='--', linewidth=0.6, color='black', label=r'\parbox{7em}{95th percentile\\regression}')

plt.scatter(X, Y, color='grey', alpha=0.2, edgecolors='none')
#plt.xlabel("100 typ oprs")
plt.xticks([0,25,50,75,100], ['0','25','50','75', 'operators'])
ax = plt.gca()
#ax.xaxis.get_majorticklabels()[3].set_horizontalalignment("right")
plt.yticks([0,100,200,300,380], ['0','100','200','300','380\napps'])

plt.legend(framealpha=0.1)
plt.show()


