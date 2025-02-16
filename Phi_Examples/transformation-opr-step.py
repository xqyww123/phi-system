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
print(summary_quad)

x_range = np.linspace(X.min(), X.max(), 100)
y_fit = quantile_model_quad.params['Intercept'] + quantile_model_quad.params['X'] * x_range


# 预测值
y_pred = quantile_model_quad.predict(data['X'])

# 计算 SSR (残差平方和)
ss_residual = np.sum((data['Y'] - y_pred) * (data['Y'] >= y_pred))  # 95th 百分位的残差处理

# 计算 SST_0 (无解释变量模型的平方和，假设只有截距)
y_mean = np.percentile(data['Y'], 95)  # 使用 95th 百分位作为基线
ss_total = np.sum((data['Y'] - y_mean) * (data['Y'] >= y_mean))  # 总平方和调整为 95th 百分位

# 计算伪 R-squared
pseudo_r_squared = 1 - (ss_residual / ss_total)
print(f'Pseudo R-squared value: {pseudo_r_squared}')



plt.figure(figsize=(4, 4))
plt.plot(x_range, y_fit, linestyle='--', linewidth=0.6, color='black', label=r'\parbox{7em}{95th percentile\\regression}')

plt.scatter(X, Y, color='grey', alpha=0.2, edgecolors='none')
#plt.xlabel("100 typ oprs")
plt.xticks([0,25,50,75,100], ['0','25','50','75', 'operators'])
ax = plt.gca()
#ax.xaxis.get_majorticklabels()[3].set_horizontalalignment("right")
plt.yticks([0,50,100,150,200,250], ['0','50','100','150','200','250\napps'])

plt.legend(framealpha=0.1)
plt.show()


