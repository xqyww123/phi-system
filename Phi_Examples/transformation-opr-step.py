import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
import pandas as pd
import statsmodels.formula.api as smf
from matplotlib.ticker import MaxNLocator

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

plt.plot(x_range, y_fit, color='black', label='95th percentile regression line')

#plt.title('Scatter plot with high transparency')
plt.scatter(X, Y, color='grey', alpha=0.2, edgecolors='none')
plt.xlabel("# of type operators")
plt.ylabel("LP steps")
ax = plt.gca()  # Get the current axis
ax.xaxis.set_label_coords(0.86, -0.025)
ax.xaxis.label.set_bbox(dict(facecolor='white', edgecolor='none', pad=3))
ax.xaxis.set_major_locator(MaxNLocator(nbins='auto'))
plt.legend()

#plt.tight_layout()
plt.show()


