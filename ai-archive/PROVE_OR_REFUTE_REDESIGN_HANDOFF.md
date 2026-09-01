# 守卫竞赛重设计:compact 交接(2026-09-01)

## 一、正在飞的任务(compact 后第一优先)

**prove_or_refute 生产代码的对抗评审工作流**:run `wf_60934ca1-eb0`,task `wzkwdlsdn`。
3 质疑(conc/eleg/cons)→ 3 全新辩护 → 裁判,全 Opus 5。完成通知到达后:
中文汇总全部意见 + 被删意见及理由 + 每条修法,呈作者;**作者点头前源码一字不改**。
(上一轮同型工作流材料在 scratchpad/judge_verdict.txt 可作参照格式。)

## 二、本地源码状态(未提交,等作者裁定 commit)

对安全点 382407dc 的 git diff(已自查 + 实测背书):
1. `reasoners.ML` ①30ms 快证闸改"解决才算过"(`Seq.filter Thm.no_prems o search`,
   ~:1341,作者裁定"进了竞赛至少我们能给 REFUTED,必须加");②装配改分选手刀:
   `wrap budget` 包 P-auto/R-conv、`wrap hang_net(10s)` 包 R-nitpick 家族(~:1425)。
2. `guard_refute.ML` nitpick() 里模型搜索被 `Timeout.apply (#timeout params + seconds 1.0)`
   严格包住(preprocess 刀外;刀值=名义+1s 宽限,镜像 Nitpick timeout_bonus);
   refuter_probe 的 reruns/rerun_more 禁用为 ("-","-")(无统一外刀则每 none 追加
   4 次无界搜索;整套探针本就 TEMPORARY、待计划批准后拆)。
3. `Docs/GUARD_NITPICK_FALSIFY_PLAN.md` :360 与 :681 两处决策档就地标注
   2026-09-01 裁定解除(闸门统一判据 + 分选手刀)。
4. `Docs/RAUTO_VERIFY_PLAN.md`(计划草案,未批)+ `RAUTO_VERIFY_MISTAKES.md`:
   术语"娘家理论"→"来源理论"已统一。

**待作者裁定**:①commit;②默认值 5000→2000(数据支持,见下表;现 2000 只活在
cslh19 的 PLPR declare 里)。

## 三、实测终表(全部归档于 cslh19 ~/exp*_final/)

| 配置 | 目标(p/r/u) | Quicksort:47 | 竞赛墙钟 | 全链 |
| --- | --- | --- | --- | --- |
| C12(旧闸,5000 统一) | 399(49/300/50) | 驳回 | 2067s | ~1433s |
| RunA(新闸,5000 统一) | 486(47/379/60) | 驳回 | 2197s | 1521s |
| **RunB(新闸+刀,2000)** | **487(48/379/60)** | **4 变体全驳回** | **898s** | **842s** |

- 新闸解救 89 个此前静默缺席目标(78 refuted+11 undecided+0 proved,13 个理论,
  含 phi 核心区段);RunA↔RunB 共同 486 目标裁决零差异;RunB undecided 率
  60/487=12.3%(未证出口径 13.7%,与旧口径持平)。
- 旧统一刀 2000 的代价曾是恰 3 条 Quicksort:47(竞赛内选手级需 4.6-6s,
  nitpick_probe 实测);新刀下全回归。名义预算旋钮(5000/3000/2000)无杠杆。
- 波动机制已钉死:30ms 闸是"返回即过"墙钟采样(auto_search_tac 永不失败),
  改判据后 unproved 语料由内容决定;proved 类(<30ms 证出不留痕)仍闪,记录点
  上移补丁(quick_gate,agent 写好未部署,scratchpad/reasoners.ML.patched)可治,
  但优先级降(unproved 语料已确定)。
- 五轮 2000 系对照细节:T2000a/b 同配置零翻转;固定分母(五轮共同 393)下
  proved 恒 47。**多轮对照一律固定分母/共同集合,不用各轮总数**(口径教训)。
- 口径纪律(被作者严批过):谈"驳斥成功用时"必须分三口径——独立回放搜索段
  (avg 231ms/max 1038ms)、竞赛内选手级(中位 0.3-0.4s、2-4% 长尾 3-6s)、
  竞赛墙钟(账本等待,秒级)。决策引选手级+墙钟,不引实验室数。

## 四、R-auto 验证计划线(上一条主线,暂候)

- `Docs/RAUTO_VERIFY_PLAN.md` 草案 rev1 经工作流评审:3 blocker(trust-1 Var 代换
  方向反、trust-2 specification 是定义式致常量闸杀死旗舰例、process-1 37 条对照
  不存在)+12 major+6 minor+6 放宽;修订方案已呈,**作者尚未裁定修订与放宽取舍**。
- 后续新增待裁:forced-only 永久化(guess_inst 只提交 forced,实测零代价,
  exp{FO,V4}_final 数据;正式版=inst 里两行无条件闸;step_selector 缝与 del_loop
  退役联动);debt 公理 hack(Debt_Axiom.debts 账本精确过滤,genuine_modulo_debt);
  "能检皆可检"(§3.2 重定义为忠实搬运,Abs_mat 等一律可代换);矩阵扩展项低优先。
- 评审材料:scratchpad/review_result_{0..5}.txt(33 条)+ judge_verdict.txt。

## 五、边界与禁区

- **Interrupt_Breakdown 问题已由作者派另一 agent 修,我方不再触碰**(含相关
  上游报告、lazy.ML/future.ML 修复草案、reasoners.ML:1399 Lazy 共享等中断族项)。
- Option 雷(`the NONE`,basics.ML:84;头号嫌疑 Provers/order_tac.ML:142 裸 the,
  全局 HOL unsafe solver;探针 P1/P2/P4 备好未跑)——与 Breakdown 同族,
  **未经作者明示不动**,避免与另一 agent 冲突。
- 永不跑 isabelle build;.ML 改动重启 REPL 即生效;计划文档禁脚本改;
  不 stash/checkout/clean;commit 只在 main 且须作者令。

## 六、cslh19 现场

- 工作树 = 本地新源码(reasoners 6db08b6f / guard_refute 4d24b969)+ PLPR 带
  declare [[guard_race_timeout=2000, guard_refute_timeout=2000]](077c75ee);
  REPL 在 6669 跑着新设计。恢复安全点=scp 本地 git show HEAD 版三文件+重启。
- 台架:run_probe.py(评 PhiEx_All,判据=日志 `ERRORS RETURNED: None` 且无
  REPLFail/EXC + 真实 ELAPSED + 全新 REPL);重启流程=杀 poly/repl_server/java
  REPL 树 + mv event_log 归档 + nohup setsid start_repl.sh + 等 6669;
  zsh 会吞 ===,一律 bash -s。分析脚本模式:guard_race XML 逐 record 取
  theory/line/goal 键 + verdict/winner/elapsed。
- 无验证评测资产:eval_unverified.ML + Scratch_UV_*(9 来源理论);
  unverified_eval.tsv(330/335 可读,R-nitpick 86.1%,smbc 30.9%,并集 88.8%,
  增量 +9 含 0143);run_nun_sweep.sh。

## 七、监视纪律

长任务 ≤10 分钟监视(Monitor 循环 ssh 探progress;工作流例外——作者豁免过
评审工作流的 monitor)。
