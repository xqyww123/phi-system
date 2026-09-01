# R-auto verifier 重写前的错误全录（2026-08-31）

> 用途:作者裁定第一版 R-auto verifier "基本上是乱写的",已整体删除(工作树恢复到
> phi-system 安全点 382407dc,本地与 cslh19 两侧均已恢复)。本文档记录第一版犯过的
> 全部错误、必须尊重的环境事实、已量化的数据与资产坐标,供 compact 之后重写
> `Docs/RAUTO_VERIFY_PLAN.md`(新计划,尚未动笔)时逐条对照。重写计划须经作者批准
> 后才许写实现代码。

## 〇、名词与背景(一句话版)

守卫竞赛 `prove_or_refute`(reasoners.ML)有 P-auto / R-conv / R-nitpick 三类选手。
本轮工作:①新增 R-nunchaku 选手(黑盒翻译 + smbc 当取值神谕);②给 R-nitpick 与
R-nunchaku 的反例加"R-auto 验证"——作者亲定的判据:把反例的取值代换进目标,看能否
被化简机器化成 False。第一版实现被删,原因如下。

## 一、设计层错误

1. **误读作者的 "R-auto 验证" 提议**。作者从最初就是指"代换后用化简机器看能否化成
   False";我先擅自实现成"代换后重跑 Phi_Nitpick(card 1-10)确认",绕了一整圈弯路,
   还搭进去一个取值收缩循环(那是 Nitpick 有限作用域才需要的东西,simp 符号求值根本
   不需要)。教训:作者提议先复述确认语义再动手。
2. **可译值白名单是手抄的**(Nil/Cons/Pair/Some/None/True/False/数字)。正确判据是
   原则化的:"值由构造子递归构成"应查 `Ctr_Sugar` 构造子注册表,而不是列举;phi 数据
   类型构造子(`Addr`、`Block`、`AgIdx_N`……)全被误丢——0143 模型里现成的
   `addra := Addr Null []` 被扔掉。
3. **抽象原子完全没做**(作者亲自指出)。裸原子值(`v = a₁`)整行跳过,造成 R-nitpick
   侧 96/195 条 no_pairs。正确形状:同一原子 ↦ 同一个 fresh variable(一次调用内建
   映射表);相异原子对的区分性作为显式假设(`x₁ ≠ x₂`)挂进残余,化简用到它就落
   conditional 档,没用到不受影响。
4. **函数型取值没做**:模型的逐点函数表 `(λx. _)(a₁ := v₁, …)` 在 HOL 里可表达
   (`fun_upd` 链 + 缺省处 fresh variable),第一版直接拒收。
5. **常量代换的闸只查"类型是 nat"**。代换有定义的常量不是取实例而是换命题(评审
   soundness-3,含 `0 := 2` 的极端例)。正确的闸:该常量**无定义且无 spec 规则**
   (用 `Defs.specifications_of` + `Spec_Rules.retrieve` 判),这才是"欠指定常量"的
   可判定谓词;`addrspace_bits` 恰好过这个闸,靠注释举例不算数。
6. **三级结论没有内核对象**(评审 soundness-4)。第一版读的是证明尝试的残留
   (`Goal.init (σprems ⟹ σconcl)` 后看剩什么),"refuted_kernel" 名下没有任何 thm;
   且被驳的是 preprocess 弱化+切片后的残留,不是原守卫。正确形状:改证合取
   `σP₁ ∧ … ∧ σPₙ ∧ ¬σC`——全证出即真定理(kernel 级名副其实);残留 R 时目标状态
   本身就是定理 `R ⟹ 合取`,R 是明码标价的残余假设;化到 False = 取值与前提矛盾。
7. **"refuted_cond 的残余假设与 trust_assms 同款"这句注释是错的**(评审
   soundness-2)。trust_assms 下前提是在**保留全部定义**的有限模型里被求值过、只是
   容忍 unknown;第一版的 k 条残余前提**没被任何东西求值过**,取值又来自连定义都
   丢弃的黑盒模型——两个假设不同级,注释把弱的说成了既有的。重写时要么删除该断言、
   如实定级,要么让残余前提的可满足性成为显式义务。
8. **"proved" 一词合并两个相反信号**:取值满足守卫(神谕方向错) vs 取值违反前提
   (神谕给的点不在前提域)。诊断价值完全不同,必须分开命名。

## 二、实现层错误

9. **判据 simpset 用错**(评审 soundness-1,最重):验证用了裸 racer ctxt 的
   simpset——既缺 `\<phi>guard_refute_simp` 与 Simpset_Hooks 的规则(化简能力不足,
   unverified 虚高),又把实验 2 特意 `del_loop` 摘掉的 guess_inst looper 带了回来
   (looper 可特化 schematic 为非最一般实例,产生不健全的 "refuted")。正确形状:从
   preprocess 提出 `refute_simp_ctxt`(enhance + Simpset_Hooks.invoke + del_loop),
   预处理与验证共用一套——"判据 simpset 只有一套"成为形状事实,不靠人记。
10. **只看第一个子目标**。判据 simpset 带 splitter,化简可分裂多子目标,而反驳只需
    任一合取支为假;`False` 落在子目标 2+ 就被误报 unverified。(在"证合取"新形状下
    对应为:全部剩余子目标构成残余集,逐个收集。)
11. **代换静默不命中 + 曾据此报假成功**:Nunchaku 重建的模型左端带 dummy 类型,与
    目标的 `Free("l", 'a list)` 不 aconv,`subst_atomic` 不命中;在"重跑 Phi_Nitpick
    确认"的旧版验证下,确认目标因此等于原目标,card 1-10 盲扫自然"成功"——**我把这个
    空转的 "verified=yes" 当成果汇报过**。修法(已验证有效,重写时保留思路):左端按
    名字在目标 frees/consts 中解析真类型,取值经 `Type.constraint` +
    `Syntax.check_term` 对解析类型重检,修不好即弃。
12. **解析 Nitpick 打印文本本身就是 dirty hack**:长值被 Pretty 换行折断即静默丢对、
    `first_field " = "` 脆弱、欠指定常量的选值 Nitpick 根本不打印(结构性拿不到
    `addrspace_bits`)。正确路线:在 Phi_Nitpick 补丁副本里把**项级**模型作为返回值
    带出来(该文件本来就是带 PHI-PATCH 纪律的副本),彻底放弃文本解析。
13. **fresh 名字不卫生**:`nitpick_elem1…` 跨不同取值共用(把 `[a₅,a₇]` 与 `[a₇,a₅]`
    捏造成相等),`nunchaku_`/`nitpick_` 前缀未对目标既有 frees 避让——而正确样板
    `Variable.variant_names` 就在同一文件的 `premises_of` 里,违反了"先搜代码库、
    复用而不重造"的铁律。
14. **日志纪律不对称**(评审 soundness-5):r_nunchaku_racer 的日志全写在结果之后,
    被看门狗掐死或崩溃时一条不留;verify_model 的中断分支先 reraise 后 log。正确
    形状照抄 r_nitpick_racer:`Exn.capture_body` 包全程,先记 outcome(含 exn 名、
    Timeout、interrupted)再重抛。
15. **计量字段失实**(评审 soundness-6):`sat_ms` 实为"入口到求解器返回"的总时长
    (含 preprocess/collect/translate),计划文档里 "sat 88ms + 验证 27ms" 的拆分因此
    是错的;`tries` 恒 1;分流公理条数与 smbc 的 "(potentially spurious)" 标记这两个
    直接度量欠约束程度的量被丢弃未记。
16. **注释与实现脱节**(评审 soundness-7):多处注释仍宣称"由 Phi_Nitpick 带全定义
    确认",实现早已换成简化器。信任链的说明必须与实现同步。

## 三、竞赛集成层错误

17. **log-only 验证扰动被观测的竞赛**:验证跑在 racer 预算内、裁决写入 protocol 之前,
    最多拖 5 秒,足以翻转竞赛胜负——观测手段改变被观测对象。正确位置:裁决发布之后,
    或仅在离线评测台架启用。
18. **预算不合成**:racer 看门狗 5s,内部却是 smbc 5s + 验证 5s 各自为政——求解用满
    预算则验证必被掐死。内部预算应从看门狗余额派生。

## 四、实验与流程层错误

19. **全评测明知故犯地用八理论合并上下文**(作者极为不满的一条):我早知合并上下文
    解析损耗 105 条(§26.11 我自己记录的)、早有按理论拆分的先例(Scratch_CardB/C,
    我自己写的)、且旗舰案例 0143 恰在损耗集合里——仍为省事跑了合并版,导致
    "R-nunchaku 对硬核有无增量"这一评测的核心问题**结构上不可能被回答**,
    "增量为零"是采样假象。正确协议:按 `~/corpus_index.tsv` 分组、各条目在其来源理论
    上下文解析(预期可读 ~312/335,Bucket_Hash 的 23 条是真损耗),基线同口径重算。
20. **每一轮都过早宣告成功**:vacuous verified(见 11)、冒烟三目标通过就报"闭环"、
    未向作者预先摆明实验设计缺陷。多次违反"Verify, Don't Assume"与"先提案再动手"。
21. **实现前未把设计呈作者裁剪**:验证判据(哪个战术族、哪套 simpset)、白名单、
    评测口径都是我自选的;作者的规约本应先确认。

## 五、环境事实(重写必须尊重,非错误)

E1. **发行版 heap 内已含 stock 版 `Nunchaku_Collect`**(仅导入 Main 即可见),下游
    ML 环境合并会把同名结构盖回 stock;编译期绑定冻结不受影响,但一切后续 ML 引用
    必须走别名(第一版用 `Phi_Nunchaku_*` 别名方案,有效,可沿用)。
E2. **发行版 nun-model 文本解析器**(nunchaku_model.ML)不识 smbc 的
    `match…end`/`fun (v/N:T).`/`?__N` 语法,遇之整体 FAIL。第一版用"解析前按条目
    起始行分组、丢弃含这些形态的条目"的文本过滤(dirty hack 嫌疑);更干净的候选:
    vendored 一份扩展语法的解析器副本(条目级跳过),或改 fork 的模型输出格式
    (放宽提议,fork 是自己的、PR-first)。
E3. **Nunchaku_Reconstruct 的模型左端带 dummy 类型**(见 11)。
E4. **部署的组件 wrapper 带 `--no-spurious-models`**(保护标记盲的 stock 前端);
    racer 需 spurious 模型,第一版直接调 `nunchaku-bin` 加 `--allow-spurious-models`。
E5. **smbc 对偏函数弃权**:黑盒翻译保留白名单内函数的定义,而 `nth`/`the` 等是模式
    不完备的偏函数,窄化执行踏进无方程分支即报 `undefined_values` 弃权(全语料 81/227
    条)。设计参数:偏函数也黑盒化,或补 fresh 缺省方程全化。
F6. **fork/上游 bug 三族**(全语料计数):`DT_util.apply: not a fun` 崩溃 ×5(Opus
    agent 已完成根因调查:上游继承,ElimCopy 解码 0 元决策树,复现器
    `/home/qiyuan/.claude/jobs/0d7a3f0b/tmp/min_repro2.nun`,修复草案在调查报告里);
    nunchaku 解析不了 smbc 输出的 `match` ×11;smbc 内部断言崩溃(Solver.ml:2955)×5。

## 六、已量化数据(独立回放口径,`~/full_eval.tsv`,cslh19)

- 可读 230/335(合并上下文口径,含缺陷 19);unverified R-nitpick **195/230 = 84.8%**
  与 §26.11 基线逐位吻合(自校准通过)。
- verified R-nitpick 59(另 96 no_pairs、40 unverified);verified R-nunchaku 10
  (全部与 R-nitpick 重合,增量零——采样假象,见 19)。
- R-nunchaku 227 次调用分类:SAT 69(verified 10 / unverified 39 / no_pairs 20)、
  undefined_values 81、调度器超时 33、incomplete 22、match 解析失败 11、
  smbc 断言崩溃 5、DT_util 崩溃 5。
- 双双未驳斥 32 条 id 已存 §26.12(Binary_Trees 区段为主)。
- 历史口径澄清(勿再混淆):"当年 89.9%" 是弱竞赛漏网上的捞漏率,不是总驳斥率;
  今日总驳斥率两口径 86.3%(竞赛)/ 84.8%(独立回放)。

## 七、资产坐标

- 评审工作流(3 质问 + 3 辩护已完成,裁判恢复中,task wqq248kyo):完整材料在
  `/tmp/claude-1002/-home-qiyuan-Current-MLML/0d7a3f0b-9e6f-4b94-904c-3b48067a9a97/tasks/wttehcqhd.output`
  (soundness-1..7 全文)与
  `~/.claude/projects/-home-qiyuan-Current-MLML/0d7a3f0b-9e6f-4b94-904c-3b48067a9a97/subagents/workflows/wf_b88fba18-718/journal.jsonl`
  (六个 agent 的结构化返回,elegance/robustness 两维在此)。裁判裁决落地后并入新计划。
- 被删代码的可查副本:cslh19 `~/Current/MLML/contrib/phi-system/Phi_Examples/` 下的
  未跟踪文件 `nunchaku_collect_blackbox.ML`(黑盒收集器,补丁 2+3)与
  `nunchaku_collect_patched.ML`(Nitpick 对等语义,补丁 4)仍在;本地
  `/home/qiyuan/.claude/jobs/0d7a3f0b/tmp/` 亦有两副本及全部 Scratch_*.thy。
- cslh19:语料 `~/corpus/` + `~/corpus_index.tsv`(格式 `NNNN\t理论:行`);
  `~/full_eval.tsv`;Event_Log(`nunchaku_racer`/`refute_verify` 现役 +
  `~/event_log_prev/` 归档);Nunchaku 部署 `~/nunchaku-fork/`(bin 0.6 + 静态
  cvc5 1.3.4 + smbc 0.6.1,`NUNCHAKU_HOME` 已写入用户级 Isabelle settings);
  REPL 经 `~/start_repl.sh`。
- 实验记录:`contrib/phi-system/Docs/GUARD_NITPICK_FALSIFY_PLAN.md` §26.12
  (其中 "sat 88ms + 验证 27ms" 的拆分按错误 15 是失实的,重写计划时须勘误)。
- 安全点:phi-system `382407dc`、Performant_Isabelle_ML `ab32fbb`、父仓 `46b1df1`。

## 八、重写计划的骨架(已向作者预告,未获批,compact 后据此起草)

新文档 `contrib/phi-system/Docs/RAUTO_VERIFY_PLAN.md`:①信任模型与三级结论
(全带内核对象,证合取形);②取值提取原则化(构造子注册表 + 原子 ↦ fresh
variables + 区分性假设 + fun_upd + 欠指定常量闸;Nitpick 项级模型从补丁副本带出);
③判据 simpset 唯一化(`refute_simp_ctxt`);④竞赛集成纪律(预算派生、裁决后验证、
日志全覆盖);⑤评测协议(按来源理论解析、基线重算、37 条已证目标伪阳性对照);
⑥评审采纳表 + 放宽提议清单(逐条对应裁判裁决)。计划经作者批准后方可写实现。
