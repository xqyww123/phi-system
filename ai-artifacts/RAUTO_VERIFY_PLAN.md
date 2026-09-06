# R-auto 验证重写计划(RAUTO_VERIFY_PLAN)

状态:**已放弃(2026-09-01 作者裁定)。** 草案 rev 1 未获批准、未实施即废弃,
移入 ai-archive 仅作存档;其评审材料与修订方案一并作废。

(原状态行:草案 rev 1(2026-08-31),未获作者批准。批准之前不写任何实现代码。)

前情:R-auto 验证的第一版实现被作者裁定"基本上是乱写的",已整体删除,工作树恢复到
phi-system 安全点 382407dc(本地与 cslh19 两侧)。第一版的全部错误(21 条)记录在主仓
根目录的 `RAUTO_VERIFY_MISTAKES.md`;针对第一版的对抗评审(3 名质问 + 3 名辩护,共
33 条意见;裁判未完成)的完整材料坐标见该文档第七节。本计划从零重写设计,逐条对照
错误全录与评审意见;§10 是错误 → 落点的对照表,§6 是评审采纳表。

阅读顺序建议:先 §0(术语)与 §1(本质与信任模型),再按需读 §2–§5(设计),
§6–§8(评审采纳、放宽提议、待裁决策),§9(批准后的实施顺序),§10(错误对照)。

---

## 0 · 术语表(本文档的权威命名;同一概念全文只用同一个词)

- **守卫竞赛**:`prove_or_refute`(reasoners.ML:1340)——对一条守卫条件,证明方选手与
  反驳方选手在竞赛引擎(Performant_Isabelle_ML 的 `Race.race`)上并行竞争。
- **选手**:P-auto(经典搜索证明)、R-conv(证否定反驳)、R-nitpick(有限模型反驳,经
  Phi_Nitpick)。本轮要新增 **R-nunchaku**(黑盒翻译 + smbc 求解的模型反驳)。
- **取值神谕**:产出"哪个自由变量取哪个值"这份候选清单的模型搜索器。本计划里有两个:
  Phi_Nitpick(信任前提轨道、保留全部定义)与黑盒 Nunchaku+smbc(连定义一并丢弃,
  欠约束严格更多)。神谕的输出**一律不直接采信**,这正是要建验证的原因。
- **R-auto 验证**(本计划的主题):作者亲定的判据——把神谕反例中可检的取值代换进
  残留,交给化简机器,看能否化成 `False`。"R-auto"一名沿用作者的称呼;判据的战术族
  以化简机器为主体(作者原话"想看看在代换后是否能化简成 false"),是否附加
  "证否定"的兜底段是待裁决策 D2。
- **残留**:`Phi_Guard_Refute.preprocess`(guard_refute.ML:176)的输出 `(prems, concl)`
  ——原守卫经前提弱化钩子、判据 simpset 化简、case 拆分与变量闭包切片后剩下的形状。
  注意:残留是比原守卫**更强**的命题(弱化前提、丢前提都朝这个方向),驳倒残留不等于
  驳倒原守卫;这是既有的作者裁定(guard_refute.ML:83-86 注释),两个模型反驳选手同轨,
  本计划不改变它。
- **判据 simpset**:预处理与验证共用的那套化简上下文。本计划把它固化为一个具名函数
  `refute_simp_ctxt`(§2.1),"只有一套"从此是形状事实而非口头约定。
- **可检取值**:能被搬回 Isabelle 项、且代换后能被真实理论评估的取值(§3.2 给出
  可判定的定义)。
- **抽象原子**:神谕对无构造子类型给出的记号元素(如 a₁、a₂)。处理方式:同一原子
  映射到同一个 fresh variable,相异原子对的区分性作为显式假设(§3.2)。
- **欠指定常量**:在真实理论里既无 `Defs` 定义、又无 `Spec_Rules` 规则、也不被任何
  孤儿公理提及的常量(可判定谓词,§3.1)。只有这类常量的取值代换才是"取实例";
  代换一个有定义的常量是换命题,不是取实例。
- **验证等级**:验证对一次代换给出的分级结论(§1.3 的等级表);每一级都携带内核对象
  或明码标价的残余假设。
- **残余假设**:某一验证等级成立所额外依赖、但未被机器消掉的假设(如
  "k 条化简不动的前提在该取值下联合可满足")。
- **黑盒翻译**:vendored 收集器副本 `nunchaku_collect_blackbox.ML` 的语义——白名单外
  常量不追定义与 spec 规则(成为不解释的 val),触及它们的孤儿公理被分流。
- **台架**:离线评测驱动(cslh19 上按语料逐条回放的脚本),与生产内的守卫竞赛相对。
- **来源理论**:`corpus_index.tsv` 为每条语料记录的理论(格式 `编号→理论:行`)——
  该守卫当初被转储时所在的理论;评测必须在它的上下文里解析该条目(§5.1),
  合并多个理论的上下文会因语法冲突丢条目。

---

## 1 · 本质与信任模型

### 1.1 一句话本质

R-auto 验证是给"模型式反驳"补的一道机器检验:神谕说"这组取值让守卫为假",验证就把
这组取值真的代进残留,在**保留全部定义的真实理论**里用化简机器算一遍,看它是否真的
化成 `False`——化成了,这次反驳就从"神谕的一面之词"升级为"带内核对象的已检验事实"。

### 1.2 为什么需要它(信任链的位置)

两个神谕各有系统性的说谎方式:Phi_Nitpick 在 `user_axioms = false` 下无视用户公理,
黑盒 Nunchaku 更是连定义一起丢,smbc 可以自由发明白名单外常量的解释。所以裸 SAT
永不采信。验证的职责恰是把神谕的欠约束补回来:代换后的评估发生在带全部定义的真实
理论里,凡是靠"发明了不该发明的解释"得来的假反例,理应在这里被拒掉(表现为
Premise_False 或 Guard_Holds,见 §1.3)。**verified 率低于 SAT 率是设计使然,不是缺陷。**

### 1.3 验证等级(提案,命名待作者批准,决策点 D7)

判据机制(§2.2,推荐 conv 形)对代换后的残留 `σP₁ ⟹ … ⟹ σPₙ ⟹ σC` 产出一条内核
等式 `σgoal ≡ rhs`,等级从 rhs 读出:

| 等级 | rhs 形状 | 内核对象 | 残余假设 | 对反驳的意义 |
| --- | --- | --- | --- | --- |
| `Refuted_Kernel` | `False` | thm `σgoal ≡ False` | 无(相对残留) | 反驳确认,满格 |
| `Refuted_Cond k` | `R₁ ⟹ … ⟹ R_k ⟹ False` | thm `σgoal ≡ (R ⟹ False)` | R 在该取值下联合可满足 | 反驳成立当且仅当残余假设成立;是否采信待裁(D3) |
| `Guard_Holds` | `True`,且逐条前提单测均非 `False` | 同一条 thm | 无 | 神谕方向错:取值满足守卫 |
| `Premise_False` | `True`,且某条 σ前提单测为 `False` | 该前提的 `≡ False` | 无 | 取值不在前提域内(神谕给的点白给) |
| `Unverified` | 其它形状 | 同一条 thm(未达结论) | — | 化简机器够不着,不采信 |
| `Verify_Timeout` | (超时) | 无 | — | 预算内没算完 |
| `Substitution_Noop` | (代换未命中) | 无 | — | 结构性故障信号:取值对非空但 σgoal 与原式相同,必须显式报出,永不静默归入其它等级(错误 11 的教训) |

三点说明:

1. **每一级都有承载物**。`Refuted_Kernel` 名下真的有一条内核定理;`Refuted_Cond` 的
   残余假设不再从别的形状里推断,而是定理右端明摆着的 k 条前提。这修掉错误 6
   ("三级结论没有内核对象")。
2. **`Guard_Holds` 与 `Premise_False` 必须分开**(错误 8):前者说神谕方向错了,后者说
   神谕给的点根本不满足前提——诊断价值完全不同。区分手段:rhs 为 `True` 时,对每条
   σ前提单独跑一次同一判据化简,看是否有 `≡ False` 者(代价极小,前提已是基本 ground 的)。
3. **与 trust_assms 轨道的关系必须如实定级**(错误 7):`Refuted_Cond` 的残余假设与
   Phi_Nitpick trust_assms 轨道**形状同款、强度不同**——trust_assms 的取值出自保留
   全部定义的模型且前提在有限模型里被求值过(只容忍 unknown),这里的 k 条前提没被
   任何模型求值过,取值还可能出自连定义都丢的黑盒。注释一律按这个措辞写,不许再写
   "同款假设"。

另外每个 `Refuted_*` 结论都随身携带:实际代换的取值对清单、其中常量代换的清单
(§3.1)、以及为抽象原子引入的 fresh variables 与区分性假设清单——让读日志的人不需要
交叉对齐第二个日志类别就能知道这次反驳"花了什么代价"(评审 elegance-7)。

### 1.4 能做到 100% 有效吗(作者之问,如实回答)

分两个方向,答案不同。

**健全方向(被确认的反驳是否可信)——`Refuted_Kernel` 这一档可以做到机器检验意义上的
满格,但有两条结构性天花板,都不是验证能修的:**

1. **验证的对象是残留,不是原守卫。** preprocess 的前提弱化与切片让残留是更强的命题,
   驳倒残留不必然驳倒原守卫。这是既有作者裁定(与 R-nitpick 同轨,代价是完备性:
   一条被误判为假的守卫只是少用一条推理规则),验证不叠加新的不确定,但也消不掉这层。
2. **`Refuted_Cond` 的残余假设原则上不可消除。** 化简机器不是判定过程,总有前提化不动;
   它们的联合可满足性只能作为显式假设。能做的是:(a) 显式化并带内核对象(已做进
   等级表);(b) 用 37 条 P-auto 已证目标做伪阳性对照,实测这一档的真实误率(§5.3);
   (c) 由作者拿着数字裁定这一档是否采信(D3)。此外常量代换那一路,即使加了欠指定闸
   与规约检查(§3.1),仍有一个已知盲角:被 PATCH 3 分流的孤儿公理可能约束着该常量,
   而 `Spec_Rules`/`Defs` 看不见它——所以闸里加了"被孤儿公理提及即不代换"这一条,
   把盲角关掉,代价是完备性。

**覆盖方向(每个真反例都能被确认)——达不到 100%,困难有四条,都是结构性的:**

1. **化简机器不是判定过程。** 偏函数(`nth`、`the`)出定义域、特征方程不全的常量、
   不触发的条件重写规则,都会让一个真·为假的 ground 命题化不到 `False`,落
   `Unverified`。
2. **抽象原子只能部分检验。** 无构造子类型的原子映射成 fresh variables 加区分性假设
   后,残留里仍是自由变量,化简可能停住——这类反驳天然只能到 `Refuted_Cond` 或
   `Unverified`。
3. **神谕的一部分输出本来就该被拒。** 黑盒模型与 `user_axioms = false` 的模型里混着
   伪反例,验证的天职就是拒掉它们;所以 verified 率的上限不是 SAT 率,而是
   "SAT 中真反例的占比"——这个占比本身没人知道,只能靠对照实验逼近。
4. **预算有限。** 验证跑在选手看门狗之内,深的符号求值可能超时。

结论:**验证能把"采信的反驳"做到每条都带内核对象、每条残余假设都明码标价——这是
100% 的诚实;但它做不到"每个真反例都确认"的 100% 覆盖,也做不到"驳倒残留 = 驳倒
原守卫"的 100% 语义强度。** 本计划的全部设计都在把 kernel 档的占比推高(项级模型、
构造子注册表、fun_upd、正确的判据 simpset),并把剩下的每一分不确定显式化、可测量。

---

## 2 · 判据:机制与形状

### 2.1 判据 simpset 唯一化(修错误 9;评审 soundness-1 / elegance-2 / robustness-1,三方一致)

从 preprocess 里把构造化简上下文的那几行(guard_refute.ML:181-190)提成具名函数并导出:

```
val refute_simp_ctxt : Proof.context -> term -> Proof.context
(* Guard_Refute_SS.enhance ctxt
   |> Simpset_Hooks.invoke (Context.Proof ctxt) ()
   |> fold Splitter.add_split (case_splits ctxt t)
   |> Raw_Simplifier.del_loop "inst_var_by_Ctr_sels" *)
```

preprocess 对 `prepared` 调它;验证对**代换后的**目标调它(case_splits 按代换后的项
重算)。效果:验证既拿到 `\<phi>guard_refute_simp` 与 Simpset_Hooks 贡献的全部规则
(缺了它们 phi 词汇化不动,unverified 虚高),又不会把 preprocess 特意摘掉的
guess_inst looper 带回来(looper 自行特化 schematic 是不健全方向)。"判据 simpset
只有一套"从此由函数存在性保证。

del_loop 的删除对象是**化简机器自己挑实例**的行为;神谕给 schematic Var 定值再由我们
代换,是另一回事(见 §3.1 第三条)。

### 2.2 判据机制的形状(决策点 D1;推荐 conv 形)

两个候选,差别在"内核对象怎么来"与"case 拆分还能不能用":

**候选 A(推荐):`Simplifier.asm_full_rewrite`(conv 形)。** 对
`σP₁ ⟹ … ⟹ σPₙ ⟹ σC` 整体跑判据上下文的 asm_full 改写,直接返回内核等式
`σgoal ≡ rhs`。优点:(i) 内核对象免费到手,三级结论全部从 rhs 读出,一次调用;
(ii) 前提互相化简的能力原生保留(asm 模式化前提时用得上前面的前提)——0143 那类
14 条前提互化剩 11 条的行为不变;(iii) 没有子目标概念,错误 10(只看子目标 1)整个
消失。缺点:conv 不跑 looper(已核实:`Splitter.add_split` 装的是 loop tactic,
splitter.ML:443-453;loop tactic 只在 `generic_simp_tac` 战术层生效),所以验证侧
**case 拆分不可用**。

这个缺点经分析很小,理由:验证时 case-over-free 几乎不存在——(a) 拿到取值的自由变量,
其 case 变成 case-over-constructor,靠普通 case 方程即可归约,不需要 splitter;
(b) 抽象原子来自无构造子类型,该类型根本没有 case 常量;(c) 残留本身是 preprocess
带 splitter 化简后的不动点,旧的 case-over-free 已拆完。剩余暴露面只有"没拿到取值的
数据类型自由变量上的 case",落 `Unverified`,损失是完备性且可在台架上计数。

**候选 B:否定目标 + `asm_full_simp_tac`(tactic 形)。** 对
`σP₁ ∧ … ∧ σPₙ ∧ ¬σC` 建 Goal.init 跑战术:全证出即拿到真定理(kernel 档),剩余
子目标构成残余集(全部收集,不只看第 1 个)。优点:splitter 可用。缺点:合取形下
前提互化默认不可用(HOL 默认 simpset 不把 conj 当带假设的 congruence),0143 类
行为要重新标定;残留读取与定理装配比 conv 形多一段机器。

**推荐 A**,并把"若台架数据显示 case-over-free 的 Unverified 占比可观则改走 B"写成
显式的回退条款。错误全录 §一.6 里记的"改证合取"是评审质问方的原始提案;辩护方
(soundness-4)指出合取形丢前提互化的代价并给出 conv 方案,本计划采辩护方——**此处
与错误全录的记载有偏离,特请作者注意并裁定(D1)。**

落地前必须先跑的 REPL 探针(§9 阶段 0;Verify, Don't Assume):
- `asm_full_rewrite` 对 `True ⟹ False` 等形状是否归约出 `≡ False`(即 conv 是否消
  已化为 True 的前提)——若不消,判据在 conv 外补一层 `Object_Logic`/伪前提消除,或
  改推荐 B;
- 判据上下文里带 split 规则但走 conv 时的行为(应为不触发、不报错);
- `asm_full_rewrite` 在带 fresh variables 的非 ground 残留上的停点形状。

### 2.3 R-nitpick 验证路径的 Var 屏蔽(纵深防御;评审 soundness-1 辩方建议)

即使 del_loop 已随 `refute_simp_ctxt` 进入验证,R-nitpick 侧仍保留一道结构闸:残留中
存在**未获神谕取值**的 schematic Var 时,该 Var 保持原样进入化简(∀-闭包语义,与
R-nitpick 现行口径一致);若未来有人把 del_loop 拆掉,这道口径说明是审读者的路标。
神谕给了值的 Var 按 §3.1 第三条代换。

---

## 3 · 取值提取:原则化

### 3.1 左端:什么允许被代换

1. **目标自由变量:永远合法。** `premises_of` 把 `⋀`-约束子固定成 Free
   (guard_refute.ML:108-117),对 Free 代任何值都是全称句的合法实例(∀-见证论证)。
2. **常量:只有欠指定常量,且附带规约检查。** 闸(可判定,修错误 5):
   `Defs.specifications_of (Theory.defs_of thy) (Defs.Const, n)` 无 `#def`、
   `Spec_Rules.retrieve ctxt (Const (n, T))` 为空、且不被黑盒收集器分流的孤儿公理
   提及(第三条关掉 §1.4 说的盲角)。规约检查(评审 robustness-3 放宽提议,采纳):
   把被代换常量的规约(specification 公理,在取值处实例化)并进验证目标,**必须化为
   `True`** 才算通过——`addrspace_bits := 4` 会带出 `0 < 4`(机器检查,不再靠人工
   核对),而一个有定义常量若漏过闸,其定义方程会当场化成 `4 = 8` 而拒掉。类型仍限
   一阶可检类型(nat 起步),但注释必须写明:承担正当性的是欠指定闸,类型条件只是
   工程限制。
3. **schematic Var:神谕给了值的,照 Free 一样代换。** 信任语义:R-nitpick 的 falsify
   本来就 ∀-闭包残余 Var,反例宣称的是"对 Var 的每个取法中的这一个,守卫为假",与
   现行 R-nitpick 的宣称同强度;验证代入神谕选的那个值,检验的正是同一句话。作者当初
   的原话也是"只把 the free/schematic variables 以及部分白名单中的 constants 代换"。
   没给值的 Var 见 §2.3。

### 3.2 右端:可检取值的可判定定义(修错误 2、3、4)

一个取值项可检,当且仅当它自底向上由以下四类原子构成:

1. **注册构造子**:项头是某 `Ctr_Sugar.ctr_sugar_of` 注册的 (co)datatype 构造子——
   查注册表,不再手抄清单;phi 数据类型构造子(`Addr`、`Block`、`AgIdx_N`……)自动
   进来,0143 的 `addra := Addr Null []` 不再被扔。
2. **数字字面量**(numeral 语法,含 0/1)。
3. **抽象原子 ↦ fresh variable**:一次验证调用内维护一张原子映射表——同一原子处处
   同一个 fresh variable(修错误 13 的另一半:`[a₅,a₇]` 与 `[a₇,a₅]` 不再被捏成相等);
   相异原子对的区分性(`x₁ ≠ x₂`)作为显式假设并进验证目标,化简用到它就落
   `Refuted_Cond` 档,不用则无影响。新鲜性不靠名字前缀:先
   `fold Variable.declare_term (concl :: prems)`,再 `Variable.variant_names` 批量取名
   ——正确样板就在同文件 `premises_of` 里(修错误 13)。
4. **逐点函数表 ↦ `fun_upd` 链**:`(λx. d)(a₁ := v₁, …)` 译成 fun_upd 链,缺省处 d
   用同一套 fresh variable 机制(修错误 4)。

四类之外(神谕的内部记号、不可表示值等)一律判不可检,丢该取值对并计数(§4.3)。

### 3.3 Nitpick 侧:项级模型,彻底放弃文本解析(修错误 12)

在 Phi_Nitpick 补丁副本(该文件本就带 PHI-PATCH 纪律)里新增一处补丁:把重建后的
**项级**模型(自由变量/欠指定常量 → 取值项)作为返回值带出,替代解析 Pretty 打印文本
的整条路——换行折断、`first_field " = "`、"欠指定常量的选值根本不打印"(0143 拿不到
`addrspace_bits` 的结构性原因)一并消失。补丁范围在实施时按 Nitpick 内部的模型重建
数据结构定,原则:只取"重建为 Isabelle 项"之后的数据,不碰重建之前的内部表示。

### 3.4 Nunchaku 侧:重建类型解析与模型文本(环境事实 E2/E3)

- **重建左端带 dummy 类型**(E3):按名字在残留的 frees/consts 里解析真类型,取值经
  `Type.constraint` + `Syntax.check_term` 对解析类型重检,修不好即弃——第一版此修法
  已验证有效,保留。并加**代换命中检查**:取值对非空而 σgoal 与原式相同 ⇒ 报
  `Substitution_Noop`,永不静默(错误 11 的直接教训:上一版这里空转还报了成功)。
- **模型文本**(E2,smbc 的 `match…end`/`fun (v/N:T).`/`?__N` 令 stock 解析器整体
  FAIL):三条候选——(a) 文本过滤加固:trim 后再判条目起始/收尾,三条结构假设任一
  不成立显式记 `model_text_unrecognised`,并把"见到几组/保留几组/解析出几条/解析成功
  几条"四个计数写进日志;(b) vendored 一份扩展解析器副本,在 token 层按 `val`/`type`
  关键字重新同步做条目级跳过(**不可**按条目终结符 `.` 同步——lambda binder 里也有
  点,辩护方已指出);(c) 改 fork 的模型打印器,加"只印一阶可解析条目"开关(fork 是
  自己的,PR-first)。**推荐 (a) 立即做 + (c) 立项(D8);(b) 挂起**,等台架计数证明
  文本层加固不够再动——多一份发行版副本是每次 rebase 都要付的账。
- 过滤退化方向已核实是安全的(辩护方走查):任何解析失败只会丢取值对落 `Unverified`
  /`no_pairs`,不可能伪造反驳——神谕层的故障被验证层结构性兜住。

### 3.5 subst 纪律(评审 soundness-10 / robustness-6)

上下文固定等式 `x ≡ c`(subst)只在 R-nunchaku 侧预代换进 assms 再跑 preprocess,让
神谕与验证面对同一条公式;R-nitpick 侧**不动**——已核实 stock Nitpick 的
`pick_nits_in_subgoal` 同样只代换目标不代换 assms,R-nitpick 现行为与发行版逐字一致,
改它是另一次实验,须单独裁定。验证侧 subst 优先于神谕取值(事实压过猜测,方向正确,
维持),但被 subst 遮蔽的神谕取值对要在日志里单列(`shadowed_by_subst`),不再静默。

---

## 4 · 竞赛集成纪律

### 4.1 验证的位置(修错误 17)

- **R-nunchaku:验证是它唯一的 Refuted 通道**,跑在选手体内、预算内——这不是
  "观测扰动竞赛",而是该选手的本体。
- **R-nitpick:验证是 log-only 的对照观测**,一律**只在台架启用**(config 默认关,
  台架显式开)。生产竞赛内不跑:跑在裁决之前会拖竞赛(最多一个验证预算),跑在裁决
  之后会被竞赛终场的取消掐掉且样本有偏。台架本来就是 §5 评测协议的执行场所,对照
  数据从那里来。

### 4.2 预算(修错误 18;决策点 D6;推荐方案 A)

三个数各自独立、固定(沿 2026-08-28 作者裁定"搜索预算不为预处理买单、跨目标可比"):

- `\<phi>nunchaku_timeout`:**声明单位改为秒(整数)**——已实测 nunchaku 的
  `--timeout` 只吃整数秒,毫秒 config 除 1000 是假精度;默认 **3**(必须小于看门狗,
  写进 config 注释);
- `\<phi>refute_verify_timeout`:验证预算,默认 **1500 ms**;
- `\<phi>guard_race_timeout`(5000 ms)照旧是每条选手的看门狗。

约束"solver + verify + 预处理中位 < 看门狗"写进两个 config 的注释与本计划;辩护方
robustness-2 的信封方案(选手入口记 deadline、各段从余额支取)作为方案 B 备案——它
让"solver 饿不死验证器"成为形状事实,但让各段耗时跨目标不可比,与 2026-08-28 裁定
相抵,若作者愿意为 R-nunchaku 单独放宽该裁定则改走 B。同时把 reasoners.ML:1302-1308
与 :1421-1426 两段互相矛盾的看门狗注释对齐(前者说"只管 P-auto 和 R-conv",后者与
代码说"管每一条选手";后者是现状)。

### 4.3 日志纪律(修错误 14、15;评审 soundness-5/6)

- **选手全程 `Exn.capture_body` 包住,先记 outcome(含 exn 名、Timeout、interrupted)
  再重抛**——逐字照 r_nitpick_racer(reasoners.ML:1273-1297)的形状;验证的中断分支
  也先记一条 `interrupted` 再 reraise。
- **阶段标记**:preprocess 完、translate 完各记一条,看门狗的刀落在哪一段从此可见。
- **计量如实**:`sat_ms` 只量求解器调用那一段;preprocess/translate 各自计时,与
  refuter_probe 已有的 `pre_ms` 命名对齐;删掉恒为 1 的 `tries` 字段;**分流公理条数**
  记进日志(直接度量欠约束程度;0143 实测 17 条);smbc 的 "(potentially spurious)"
  标记**不记**——黑盒路径上它恒为真,是噪声(辩护方 soundness-6,采纳)。
- **等级直达选手日志**:验证等级(datatype)经 `string_of_grade` 写进选手自己的记录,
  批量分析不再要求两个日志类别对齐(评审 elegance-7)。
- §26.12 那张表里 "sat 88 ms + 验证 27 ms" 的拆分按上述定义是失实的,勘误随本计划
  落地(§5.6)。

### 4.4 异常纪律

- **具名承接收集器的六个"翻译不了"异常**(`TOO_META`、`CYCLIC_DEPS`、`TOO_DEEP_DEPS`、
  `UNEXPECTED_POLYMORPHISM`、`UNEXPECTED_VAR`、`UNSUPPORTED_FUNC`;须经
  `Phi_Nunchaku_Collect` 别名引用副本自己的构造子),映射到 give_up
  (`untranslatable: …`)——"这个守卫翻译不了"是常规出口,不是崩溃;其余异常照竞赛
  纪律原样上抛成 Crashed。这正是"不许 `handle _`"纪律要求的形状,不是违反。
- **删掉 R-nunchaku 路径上的 `Output.Protocol_Message` 吸收**。已到发行版源码钉死
  (isabelle_system.ML:66-115):`bash_process` 走 socket server
  (`bash_process_address`),无 server 时抛 `Fail`,全程不经 `Scala.function`——
  该异常在这条路径上没有任何来源,吸收它只会吞掉真故障。(评审两位辩护方在此互相
  矛盾,本计划以源码为准;r_nitpick_racer 的同名吸收保留,它那边 Kodkod 走 Scala peer
  的理由仍成立。)

### 4.5 装配(评审 elegance-10 / robustness-8 / soundness-11 / robustness-10)

- **共享筛选,不共享 preprocess。** 两族反驳选手的装配骨架(tvar 筛、assms 取一次、
  逐子目标 `extract_fixed_frees`、编号命名)提成唯一一份 payload;但 preprocess
  **不做**跨选手共享的 `Lazy`——已核实 lazy.ML:98-118:计算线程被自己的看门狗中断时,
  同刻的等待者会看见同一个中断("semantic race" 注释原文),即 R-nunchaku 可能死于
  R-nitpick 的超时。两位辩护方在此矛盾,以源码为准。preprocess 翻倍的代价
  (中位 0.4 s ×2)如实接受,复用问题挂进已备案的 `\<phi>guard_race_timeout` redesign。
- **可用性探针在装配处**:`NUNCHAKU_HOME` 非空**且** `$NUNCHAKU_HOME/nunchaku-bin`
  存在可执行(发行版自带 nunchaku-0.5 组件会无条件设置 NUNCHAKU_HOME,光查环境变量
  必然误判——辩护方已实测),结果按 home 值为键缓存;探测失败则该族选手不装配并
  warn 一次。不再让每条守卫白付 preprocess+collect+translate 才发现没装求解器。
- **删掉 nunchaku 装配块里抄来的 `Config.put Kodkod.kodkod_scala true`**(死配置)。
- 读取 `Process_Result.rc` 并按发行版词汇分类(126 = Cannot_Execute、127 = Not_Found、
  TIMEOUT),give_up 的 stage 带上分类;`Bash.timeout` 给外部进程一个略大于求解预算的
  硬上界。

### 4.6 黑盒收集器副本的治理(评审 elegance-5/8/11、robustness-7)

- **第四补丁,一个 token:`sound = false`**(nunchaku_collect_blackbox.ML 的返回记录)。
  副本存在的意义就是欠约束,它产出的 SAT 永远不许被读成 genuine 模型;这恰是发行版
  `sound` 字段的本义(stock 写死 true 只因 stock 从不欠约束)。附注释;计算式的
  sound(线一路穿出 consider_term)不做——那是真逻辑,会成为 rebase 最难重放的补丁。
- **打过补丁的入口改名 `isa_problem_of_subgoal_blackbox`**(signature 同步,结构名
  保持 `Nunchaku_Collect` 不变):误写 stock 名字的代码从"静默拿到 stock 收集器"变成
  编译失败。五个别名保留,但 PLPR.thy 的注释改写成"只有 Collect 这个别名承载真语义
  (heap 遮蔽防线),其余四个是命名一致性"。
- **白名单策略搬出副本**:新建小文件 `nunchaku_policy.ML`(`Phi_Nunchaku_Policy`,
  在副本**之前**装载——装载顺序是硬约束),副本内 PATCH 2 收缩成一行
  `fun opaque_const s = Phi_Nunchaku_Policy.is_opaque s`。名单本体:**立即把 `Int`
  补进清单**(`Int.nat` 是已核实的欠近似缺口,语料的 C 数组守卫前提里就有
  `nat (int i + j)`),并在注释里如实写明:这是一张为 0143/0003 实测调出来的清单,
  不是"plain HOL"的定义;放宽边界会把定义闭包放回问题里,而定义闭包正是后端解不动
  的东西(§26.12 补丁 4 实测)。**"改成按 Main 祖先的 theory 身份判定"作为待测问题
  立项(D9)**,不作为可直接落的修复——决定它需要在新旧两个边界上各跑一遍 §5 的
  批量评测。
- `value_const_whitelist`(§3.2 已改为构造子注册表,该名单大幅缩水或消失)若仍有
  残余清单,与 Policy 并置并加载期断言其相容,不做派生(两者治理的是不同问题:
  解释层 vs 搬运层)。

---

## 5 · 评测协议(修错误 19;台架执行)

1. **按来源理论解析**:语料按 `~/corpus_index.tsv`(`NNNN\t理论:行`)分组,每条在其
   来源理论的上下文里解析;预期可读 ~312/335(Bucket_Hash 的 23 条是真损耗)。**不再使用
   八理论合并上下文**——上次它把 105 条(含旗舰 0143)排除在外,令评测的核心问题
   结构上不可回答。
2. **基线同口径重算**:unverified R-nitpick 的驳斥率在同一可读集上重算(上次合并口径
   为 195/230 = 84.8%,与 §26.11 自校准吻合;换口径后须重测,不得混引)。
3. **伪阳性对照**:37 条 P-auto 已证目标全部过验证门,预期零 `Refuted_*`;任何一条
   `Refuted_Kernel` 都是即刻停下来的红灯,`Refuted_Cond` 的出现率就是 D3 裁决要用的
   伪阳性率。
4. **报告口径**:verified / unverified 按等级分列(kernel 与 cond 永不合并计数);
   R-nunchaku 增量只在"0143 类可读"的前提下谈;`Guard_Holds` 与 `Premise_False`
   分列(它们是神谕质量的两个不同诊断)。
5. **运行纪律**:长任务全程定期监视,间隔 ≤ 10 分钟(CLAUDE.md);评测经台架回放,
   不碰 `isabelle build`。
6. **勘误**:§26.12 中 "sat 88 ms + 验证 27 ms" 的拆分失实(计时起点在选手入口,含
   preprocess/collect/translate),批准后在 §26.12 就地加勘误注记,并以新计时字段
   重测该表。

---

## 6 · 评审采纳表(33 条;裁判未完成,下表为质问+辩护双方材料合议后的建议,终裁在作者)

三处辩护方之间的事实矛盾已由本轮源码核查裁定,先列出:

| 争点 | 矛盾双方 | 源码裁定 |
| --- | --- | --- |
| `bash_process` 是否走 Scala peer(Protocol_Message 有无来源) | elegance-3 辩方(说走、吸收必要)vs robustness-5 辩方(说走 socket、死代码) | robustness-5 辩方对:isabelle_system.ML:66-115 走 socket server,抛 `Fail`;nunchaku 路径删吸收(§4.4) |
| preprocess 共享 `Lazy` 是否安全 | soundness-8 辩方(可共享)vs robustness-8 辩方(中断转交等待者) | robustness-8 辩方对:lazy.ML:98-118 semantic race;不共享(§4.5) |
| 0143 的 `refuted_cond:11` 归因 | robustness-1 质问方(归咎 simpset 缺规则)vs 其辩方 | 辩方对:那 11 条是黑盒里无可代换取值的 phi 前提,任何 simpset 都化不动;修 simpset 不会把 11 变 0(预期管理写进 §5) |

采纳表(“采纳”指进入本计划;“落点”指章节):

| 编号 | 判定 | 采纳 | 落点 / 说明 |
| --- | --- | --- | --- |
| soundness-1 | 辩方认领 | 采纳 | §2.1 refute_simp_ctxt;§2.3 Var 屏蔽 |
| soundness-2 | 辩方部分认领 | 采纳辩方版 | §1.3 说明 3 定级措辞;D3 先测后裁 |
| soundness-3 | 辩方认领(例子修正) | 采纳 | §3.1 欠指定闸(质问方的 0/1 例已被辩方证伪,不引) |
| soundness-4 | 辩方部分认领 | 采纳辩方版 | §2.2 conv 形(D1);"残留 vs 原守卫"是既有裁定不算新账 |
| soundness-5 | 辩方部分认领 | 采纳 | §4.3 capture_body + 阶段标记;"与没启动不可分"之说不实(exits 可分),不引 |
| soundness-6 | 辩方部分认领 | 采纳辩方版 | §4.3 计量如实;spurious 标记不记 |
| soundness-7 | 辩方认领 | 采纳 | §4.4 删吸收;注释全部按 §1.3 措辞重写(修错误 16) |
| soundness-8 | 辩方认领(共享 Lazy) | 部分采纳 | §4.5 共享筛选;Lazy 共享被 robustness-8 辩方+源码否决 |
| soundness-9 | 辩方部分认领 | 采纳辩方版 | §4.2 方案 A(默认值重定+注释约束+对齐矛盾注释) |
| soundness-10 | 辩方部分认领 | 采纳辩方版 | §3.5 只动 R-nunchaku 侧;subst 优先级维持;遮蔽可见化 |
| soundness-11 | 辩方认领 | 采纳 | §4.5 装配处可用性筛 |
| elegance-1 | 辩方部分认领 | 采纳辩方版 | §3.1 规约检查 + 常量代换入等级记录;方案 (a)(只代 Free)不采(删掉全部实测成果);其放宽(常量抽象成 free)辩方论证为伪不变式,不采 |
| elegance-2 | 辩方认领 | 采纳 | §2.1 |
| elegance-3 | 辩方认领 | 部分采纳 | 注释重写、删 kodkod_scala 采纳;其"吸收保留改理由"被源码核查推翻,按 robustness-5 删(§4.4) |
| elegance-4 | 辩方认领 | 采纳 | §4.4 具名承接 |
| elegance-5 | 辩方部分认领 | 采纳辩方版 | §4.6 一 token 的 sound = false(计算式不做) |
| elegance-6 | 辩方部分认领 | 采纳辩方版 | §3.4 方案 (a) 加固+计数;vendored 解析器挂起 |
| elegance-7 | 辩方认领 | 采纳 | §1.3 等级 datatype;is_refutation 全 case |
| elegance-8 | 辩方部分认领 | 采纳辩方版 | §4.6 Policy 文件(装载顺序);Main 祖先判据归 D9 待测;派生 value 名单不做 |
| elegance-9 | 辩方部分认领 | 采纳辩方版 | §4.5 rc 分类 + Bash.timeout;单位改秒;走 Nunchaku_Tool 公共入口挂 D8(须与 sound=false、缓存问题捆绑) |
| elegance-10 | 辩方认领 | 采纳 | §4.5 共享装配骨架 |
| elegance-11 | 辩方部分认领 | 采纳 | §4.6 入口改名;别名保留但注释重写 |
| elegance-12 | 辩方部分认领 | 采纳辩方版 | §3.2 variant_names(辩方证明碰撞不产伪驳斥,按一致性工作采纳) |
| robustness-1 | 辩方部分认领 | 采纳 | §2.1;0143 归因修正见上表 |
| robustness-2 | 辩方部分认领 | 采纳辩方版 | §4.2 单位秒+默认值;信封方案备选 D6;"零日志"之说不实,不引 |
| robustness-3 | 辩方认领 | 采纳 | §3.1(本轮唯一被双方一致定为健全性缺陷的条目) |
| robustness-4 | 辩方部分认领 | 采纳辩方版 | §3.4 (a);token 层按关键字同步的写法备档;按点同步的原提案不可行 |
| robustness-5 | 辩方认领 | 采纳 | §4.4(源码核查支持该辩方) |
| robustness-6 | 辩方大部驳回 | 采纳辩方残留 | §3.5(R-nitpick 与 stock 行为一致的事实核查采信;只修 R-nunchaku 侧) |
| robustness-7 | 辩方部分认领 | 采纳辩方版 | §4.6 补 Int + 诚实注释;判据切换归 D9 |
| robustness-8 | 辩方部分认领 | 采纳 | §4.5(Lazy 不共享的最终依据) |
| robustness-9 | 辩方认领 | 采纳 | §4.4 |
| robustness-10 | 辩方认领 | 采纳 | §4.5 可用性探针(缓存按 home 值为键,辩方的过期缓存注意事项一并采) |

### 7 · 放宽提议清单(评审发起、经辩护过滤,提请作者裁定)

1. **副本第四补丁 `sound = false`**(elegance-5):推荐**采**,一 token,最贴上游本义。
2. **fork 两件**(elegance-9/6):wrapper 透传 `--allow-spurious-models`(或环境变量),
   加"只印一阶可解析条目"的打印器开关——落地后 ML 侧的私有布局知识(nunchaku-bin
   名字、solvers/ 目录)与文本过滤大半可删。推荐**立项**(PR-first,不在本计划关键
   路径上)= D8。
3. **验证目标并入被代换常量的规约**(robustness-3):推荐**采**,已并入 §3.1 —— 它不
   是锦上添花,是常量代换健全性的正解。
4. **只认 `Refuted_Kernel` 一档**(soundness-2 质问方):推荐**不采**(现在裁会把唯一
   正面样本 0143 变成 Unknown 且失去证据来源);正确顺序是 §5.3 拿到伪阳性率后由作者
   裁 = D3。
5. **白名单改 Main 祖先判定**(robustness-7):推荐**只立项不落地**,先补 `Int`;新旧
   边界各跑一遍批量评测再定 = D9。
6. **预算信封**(robustness-2):备选 = D6,默认走方案 A。

---

## 8 · 待作者裁定的决策点汇总

| 编号 | 决策 | 推荐 |
| --- | --- | --- |
| D1 | 判据机制形状:conv(`asm_full_rewrite`)vs 否定目标 tactic | conv;台架数据触发回退条款(§2.2;与错误全录 §一.6 的记载有偏离,已注明理由) |
| D2 | 判据战术族:化简机器为主体;是否附加"证否定"(R-conv 同款)兜底段处理 Unverified | 主体化简机器;兜底段暂不做,台架先量 Unverified 的构成 |
| D3 | `Refuted_Cond` 是否采信为改变竞赛裁决的反驳 | 先 log-only 分列计数;§5.3 伪阳性率出来后作者裁;裁定前 R-nunchaku 选手保持默认关闭 |
| D4 | 常量代换三件套:欠指定闸 + 规约检查 + 孤儿公理提及即排除 | 全采(§3.1) |
| D5 | R-nitpick 验证只在台架跑(生产不接线) | 是(§4.1) |
| D6 | 预算方案 A(固定默认值)vs B(信封派生) | A(§4.2) |
| D7 | 验证等级命名(§1.3 表) | 按表;名字任凭作者改,改后全文统一 |
| D8 | fork 放宽两件立项(wrapper 透传 + 打印器开关,PR-first) | 立项 |
| D9 | 白名单 Main-祖先判据立项(先补 Int) | 立项为待测问题 |
| D10 | F6 上游报告(DT_util 复现器 + 修复草案已备)是否提交 | 遗留裁决,不阻塞本计划 |

---

## 9 · 实施顺序与验收(批准后才开始;每阶段以证据结尾,不宣告未观测的成功)

运行纪律贯穿各阶段:改 `.ML` 后重启 REPL 即生效,**不跑 `isabelle build`**;长任务
监视间隔 ≤ 10 分钟;阶段产物先给作者过目再进下一阶段。

- **阶段 0 · REPL 探针(半天)**:§2.2 列的判据机制探针;`Defs.specifications_of` /
  `Spec_Rules.retrieve` 在 `addrspace_bits` 与一个有定义常量上的实测;Ctr_Sugar
  注册表判 `Addr Null []` 可检;探针结果决定 D1 的最终形。
- **阶段 1 · 判据核心(guard_refute.ML)**:`refute_simp_ctxt` 抽取;验证函数(等级
  datatype、内核对象、`Guard_Holds`/`Premise_False` 二分探针、代换命中检查);对手写
  的三五条微型目标逐等级验收。
- **阶段 2 · 取值提取**:可检取值谓词(注册表)、抽象原子映射、fun_upd、常量三件套;
  Phi_Nitpick 项级模型补丁;Nunchaku 重建类型解析 + 文本过滤加固。0143/0148/0003
  三条历史样本作为回归锚点(须在各自来源理论的上下文里跑)。
- **阶段 3 · 选手集成(reasoners.ML / guard_refute_nunchaku.ML 重写)**:装配共享、
  可用性探针、预算、日志、异常纪律、副本治理(§4.6 四件);冒烟后给作者看日志样例,
  不报成功。
- **阶段 4 · 评测(§5)**:按来源理论全量回放 + 伪阳性对照 + 基线重算;§26.12 勘误;
  报告分列等级;D3 的数字交作者。

---

## 10 · 错误全录对照(21 条 → 落点)

| 错误(RAUTO_VERIFY_MISTAKES.md) | 落点 |
| --- | --- |
| 1 误读验证语义 | §0 术语表定义 + D2 复述确认;本计划整体即"先复述再动手" |
| 2 手抄白名单 | §3.2-1 构造子注册表 |
| 3 抽象原子没做 | §3.2-3 |
| 4 函数取值没做 | §3.2-4 |
| 5 常量闸只查类型 | §3.1-2 |
| 6 结论无内核对象 | §1.3 + §2.2 |
| 7 trust_assms 等同断言 | §1.3 说明 3 |
| 8 proved 合并两信号 | §1.3(Guard_Holds / Premise_False) |
| 9 判据 simpset 用错 | §2.1 |
| 10 只看子目标 1 | §2.2(conv 形无子目标;tactic 形收全残余) |
| 11 代换空转报假成功 | §3.4 类型解析 + Substitution_Noop |
| 12 解析打印文本 | §3.3 项级模型 |
| 13 fresh 名字不卫生 | §3.2-3 variant_names |
| 14 日志纪律不对称 | §4.3 |
| 15 计量失实 | §4.3 + §5.6 勘误 |
| 16 注释与实现脱节 | §4.4 注释重写(统一用 §1.3 措辞) |
| 17 log-only 验证扰动竞赛 | §4.1 |
| 18 预算不合成 | §4.2 |
| 19 合并上下文评测 | §5.1 |
| 20 过早宣告成功 | §9 阶段纪律(证据结尾) |
| 21 实现前未呈设计 | 本计划存在本身;D1–D10 全部先裁后做 |

环境事实:E1(heap 遮蔽→别名+入口改名,§4.6)、E2(模型文本,§3.4)、E3(dummy 类型,
§3.4)、E4(wrapper 直呼 nunchaku-bin;D8 落地后回归公共入口,§4.5/§7-2)、E5(偏函数
弃权;黑盒化边界属 D9 待测范围)、F6(上游 bug 三族;D10)。
