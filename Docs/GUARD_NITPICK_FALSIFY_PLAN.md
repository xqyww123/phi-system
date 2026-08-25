# GUARD_NITPICK_FALSIFY_PLAN — prove_or_rebute 竞速化（Nitpick / Nunchaku 反驳档）

状态：rev 3，待作者批准后从 T0 开始执行。
日期：2026-08-23（rev 1 级联插入 → rev 2 竞速化 → rev 3 吸收两轮对抗评审
（15 条意见零否决）与作者三项裁决）。

作者已裁决（写死，不再是决策点）：
- **完全替换旧实现，无总开关、无关闭分支、无逐位兼容回退**——回退手段是 git。
- **竞速架构**：30ms 串行速证保留；其后 `Par_List.get_some` 并行竞速，统一预算。
- **R-conv 采用"赛后备胎"设计**（作者与评审共同演化出的第三形态，见 §2.2）：
  其反驳不抢答、只记录，仅当竞速整体无果时才被采纳——"Refuted 不得抢在
  Proved 尚有可能时生效"由此成为结构性不变式，无需任何等待协议。

## 0 · 目标与范围

一句话：把守卫求解器 `prove_or_rebute`（`Phi_Logic_Programming_Reasoner/library/
reasoners.ML:974`）的"30ms 速证之后"部分**整体替换**为并行竞速：证明与反驳多路
选手同时开跑，第一个决定性结果终结全场；全员无果时先查 R-conv 的赛后记录，再落
入现状的（实为静默的）失败出口。新增 Nitpick 反驳选手（立即），Nunchaku 选手
（待前置工程）。

范围外（另立计划）：LLM judge（provable → defer 进 `\<obligation>` 收集，须带
`has_obligations_tag` 防御）；"第四种无声结局"的统一出口重构；Nunchaku fork/
组件/conda 分发工程；Quickcheck 前置层。

## 1 · 竞速架构

### 1.1 总体形状

**（2026-08-25 修订：竞速机器层整体由 Performant_Isabelle_ML 的竞速引擎
`Race.race`（`library/race.ML`）接管——先到认领胜出、并发认领取最小下标、
败者及时裁撤、每选手如实出口、全路径 join 屏障、中断穿透。PLPR 只保留
选手与守卫策略两层。）**

```sml
timed_tac 30ms (auto_search_tac ctxt) ORELSE (fn th =>
  let val pauto_finished = Synchronized.var "guard_race.pauto_finished" false
      val refuted_by = Synchronized.var "guard_race.refuted_by" (NONE: string option)
      val racers = (* P-auto 必须居首：并发认领取最小下标 + 串行按表序，皆偏向 Proved *)
        [P_auto ..., R_conv ...]  (* T2 追加 map R_nitpick subgoals *)
        |> map (fn (name, body) => (name, fn () => Timeout.apply budget body ()))
      val {winner, exits, forked} = Race.race racers
  in case winner of
       SOME (name, Proved th')   => Seq.single th'
     | SOME (_, Refuted refuter) => Seq.empty  (* 静默跳过；归名在 payload，胜者名可能只是转发信使 *)
     | NONE => (case Synchronized.value refuted_by of
                  SOME refuter => Seq.empty    (* 赛后记录命中 *)
                | NONE => fail)                (* 现状失败出口；将来 LLM judge 挂此 *)
  end)
```

- `datatype race_result = Proved of thm | Refuted of string`（携反驳者名）；
  选手类型 `race_result Race.racer = string * (unit -> race_result option)`
  ——只在决定性结果时返回 SOME。选手体自带 `Timeout.apply` 预算是引擎契约
  的调用方义务。崩溃诊断赛后从 `exits` 扫出（`Race.Crashed`→diag 2）。
- **子目标是选手表的一等公民**（评审 blocker 1 的修复）：每个守卫子目标一个
  R-nitpick 选手、各拿**完整**预算；目标项与变量形态在竞速前**一次性**算好共享
  （消除 §2 各选手重复计算与纪律分岔的可能）。~~并发封顶~~（**作者 2026-08-24
  裁定废除**：该条款系评审配套建议、未经作者单独裁决；依赖 future 工作线程池的
  天然上限即可，不设应用层封顶；若 T2/T5 实测出现队列挤占，凭数据重议）。
- **并行降级自动化**（评审 major 6 的修复，非配置）：由引擎承担——
  `Race.race` 在入口用 `Future.relevant` 一次判定（无内部二次降级），为假时
  按表序短路串行、语义与并行逐字一致（引擎测试电池 T7 钉死）；`forked` 字段
  如实报告实选模式。串行/并行裁决一致性仍列 T3 性质测试（消费者侧对拍）。
- 旧级联、`Falsified` 异常、`ORELSE0`（连同 `helpers0.ML:514–519` 的声明）、
  `Unsupported` 独立分支随替换**删除**。`ORELSE0` 不做惰性化修复也不独立先行
  ——它与 Pure `ORELSE` 同构且急切性在 Pure 是有意设计，直接消亡（评审 13）。
- `fail` 的文字原样保留，但计划承认事实（评审 10）：**该出口今天默认静默**
  （`warn_pretty` 以 `\<phi>trace_reasoning`（默认 0）为门，fail 用 level 1）。
  竞速的失败诊断与插桩走 config 门控的 `warning`/`Output.information`，
  **禁用 `tracing`**（无头前端超 1000 条 tracing 会永久挂死——本项目既有教训）。

### 1.2 预算

单一 Config：`Phi_Reasoner_guard_race_timeout : int Config.T`（毫秒；**作者已
确认保留为 Config 参数**，2026-08-24）。初值 **500ms**（作者原值；
700ms 上调的理由——外置 kodkodi 地板——已随单路径裁定消失），T0/T5 实测回填
终值。

**预算算术纪律**（评审 blocker 1 全部内容，实现必须逐条遵守）：
1. R-nitpick 递给 Nitpick 的名义超时 = 外层预算（单一 Scala 路径无 fudge 预扣，
   kodkod.ML:981 else 支；外置路径的"−250ms"规则随该路径弃用而废，仅存档案）；
2. `tac_timeout` 钉死 ≈0.05s（默认 0.5s 且**按候选类型逐个**计费于 Kodkod 之前
   的单调性检查，nitpick.ML:361-363——不钉死则预算死在预处理）；
3. **外层看门狗 = 预算，全体选手统一包裹**（作者裁定 2026-08-24，改写原条文）：
   不给 Nitpick 的收尾缓冲（其自包 `timeout_bonus = 1s`，nitpick.ML:938,950）留
   时间，接受两项已量化的代价——贴线命中丢失（窗口 ≈ 模型重构耗时，毫秒级；
   实测 genuine 全程 75-140ms）与"被掐超时 / Nitpick 自判 unknown"在日志中不可
   分（500ms 前自行返回的场次仍带真实裁决与耗时）。名义超时照旧传预算（规则 1
   不变）。注意模型重构**不可绕过**：其返回值 `codatatypes_ok` 参与 genuine vs
   quasi_genuine 判定（nitpick.ML:628-631），绕过 = 破坏"只信 genuine"铁律；
4. 超时串只认十进制秒（`"0.45"`；`"450ms"` 会 error 且被兜底吞掉）；
5. 预算在读取处钳制 `Int.max (1, Config.get ...)`（<1ms 对 `Timeout.apply` 意为
   **无超时**——`Timeout.ignored` 陷阱）；不设断言、不在战术内抛 error。

## 2 · 选手规格

### 2.1 P-auto（证明；表首）

`Timeout.apply budget (auto_search_tac ctxt) th`，完全解出（`SOLVED'` 同标准）
→ `SOME (Proved th')`；跑完未解或超时 → NONE。唯一能产 `Proved` 的选手；
can_inst=true 的实例化随 thm 携带。置于表首：`Par_List.get_some` 对"多选手赶在
取消生效前完成"的并列情形按表序仲裁（par_list.ML:49），表首免费偏向 Proved。

### 2.2 R-conv（证明式反驳；赛后备胎）

沿用现状 `conv_goal` 机器（结论取反、保留 ⋀/⟹ 前缀、can_inst 变量纪律照旧，
`Unsupported` = 本选手 NONE）。**关键改动**：证出否定目标后**不返回
`SOME Refuted`**，而是 `Synchronized.change rconv_refuted (K true)` 记一笔并返回
NONE（不终结比赛）。记录仅在竞速整体 NONE 时被读取（§1.1）。

不变式与论证：竞速整体 NONE ⟺ 全员失败 ⟹ P-auto 已失败——所以"R-conv 的
反驳只在 P-auto 失败后作数"由控制流结构保证，**空虚-H 守卫（H 自相矛盾时
`H ⟹ ¬C` 与 `H ⟹ C` 同时可证）永远不会被 R-conv 抢杀**：P-auto 会（通常
空虚地）证出它并以 Proved 胜出。残余不完备单侧且退化到现状：H 矛盾而 auto
两个方向都没证出 → 无果 → 跳过（= 今天）。同步安全性：记录的可见性由
`Par_List` 在 NONE 路径上 join 全部选手这一现成屏障保证，无等待、无广播、
无出口纪律。旧 D11 就此**结构性关闭**；行为相对今天的变化方向是修 bug
（今天空虚-H 守卫因 `ORELSE0` 求值顺序意外大概率被误杀），T3 探针覆盖。

代价记账：只有 R-conv 能驳倒的守卫，出局时刻从"自证完成即刻"推迟到"全场
收官"（等其余选手超时），上界 = 预算。

### 2.3 R-nitpick（每个子目标一个选手）

**变量纪律**（含评审 9 的修订）：

| 变量类 | 处置 |
| --- | --- |
| ⋀-参数 | meta 形态原样传入（Nitpick falsify 自行取反 → Skolem 存在化） |
| 冻结自由变量（fix_level=1 的假设侧+注解变量；fix_level=2 的全部） | **原样传入，零变换**（2026-08-24 作者质询后修正，原 export 设计系误设）：这些是证明方**无权**实例化的变量，Nitpick 对 Free 的"模型挑值"语义给出对一个取值的反驳——与证明侧"冻结下求证"的标准恰好对偶，无新增不对称。NO_INST（fix_level=2 全冻结）同理：存在式反驳是已接受的弱化（评审 9；现状 falsify 的 reasoners.ML:1012-1014 同向），仅损完备性。 |
| 残余 schematic Var（fix_level=1 未冻结的**结论变量**——证明方可经结论合一实例化的那批） | 原样保留——`close_form` 对否定式的 ⋀-闭包 = ¬∃vars.goal，恰为"反驳一切实例化"；Var/Free 混排形态的正确不对称已由深查矩阵 case 6 实证 |
| 语境固定自由变量 | 保持自由，其约束假设经 assms 传入（见下） |
| TFree | 原样传入（全称读法，genuine 可靠） |
| TVar | 目标或假设任一处出现 → 本选手跳过（`Term.add_tvars` 前置检测；无单态化；"代入典型类型再驳"不可靠——类型实例化亦是证明方可选） |

**对偶性说明**（评审 9 + 2026-08-24 修正，写给未来读者防抄错）：R-nitpick 的
**到达形态天然正确、零变换**——`close_form` 对 Var 的全称闭包与对 Free 的模型
挑值，恰好分别落在"证明方可实例化（结论变量）"与"证明方无权实例化（冻结
变量）"两类上。R-conv 则相反，**必须**按分支变换（can_inst=true 冻结残余
Var / false 解冻，reasoners.ML:1012-1014）——因为它的引擎是证明搜索器，对
schematic 的读法（引擎可实例化）与反驳所需的量词方向相反。两选手对同一变量
处置不同是各自引擎语义使然，均正确；不要互相"订正"。

**假设与代换**（评审 major 3 的修复）：照抄 Nitpick 自己的入口两行——
`Assumption.all_assms_of ctxt` 起手、`extract_fixed_frees` 得 `(subst, assms, t)`
且 **`subst` 真传下去**（固定等式代回）。假设传少会让"模型必须令 H 为真"的
免疫论证字面失效；传多则预算死在 `preprocess_formulas`——如需过滤，判据写进
规格并配"漏传假设致误驳"的对照探针。`def_assm_ts` 恒空（含 Var 触发穿透
ERROR 的 TERM 异常，nitpick_hol.ML:1912）。`("assms","true")` 在 Auto_Try 下是
死参数，删。

**参数构造**（评审 major 4 的修复）：`Nitpick_Commands.default_params thy` 读的
是 theory 级用户可写状态（`nitpick_params` 命令可污染；`expect` 能把每个守卫变
error 再被兜底吞成永久沉默；`overlord` 下固定文件名有并发数据竞争会产出**错
答案**）。签名分析表明逐项显式覆盖是唯一防线——钉死清单：`expect=""`、
`debug=false`、`overlord=false`、`spy=false`、`max_genuine=1`、`max_potential=0`、
`tac_timeout`（§1.2）、`sat_solver`、`card` 上限、`batch_size`。params **每场竞速
构造一次**、子目标选手间共享（`extract_params` 每次调用做 `Syntax.read_*`）。
mode 传 `Auto_Try` 只买到静默，买不到其 scope 截断与单调性强制（default_params
写死 Normal 构造）——scope/monos 限制按需在钉死清单里显式给。探针：theory 里
先 `nitpick_params [expect="genuine", overlord]` 再跑守卫，验证免疫。

**Kodkod 单路径（作者裁定 2026-08-23，双路径实测支撑）**：R-nitpick **无条件**
`Config.put Kodkod.kodkod_scala true`，外置 kodkodi 回落分支**不写**。配一个
三行的**选手可用性守卫**：进程内一次性 `can` 试调 `\<^scala>`（懒缓存），无
Scala 协议对端（Isa-REPL 裸进程）则 R-nitpick 干脆不进选手表——安全缺席，
守卫求解退回现状水平，不崩不挂不吃预算。实测依据：两路径**裁决完全一致**
（同一 kki、同一 Kodkodi 前端类、同一默认 SAT4J），差异纯在进程边界——Scala
路径 genuine 命中 ~75–140ms（0.5s 预算 10/10 存活；PIDE 会话 init 自带 warmup
服务，首调即热），外置路径每调付 ~480–700ms JVM 地板（硬 500ms 墙下命中
≈0）——为后者写回落不值。环境二分：PIDE（jEdit/MCP）与批构建有对端 →
满血；无对端 → 缺席。ROOT 的 `options [kodkod_scala]` **不加**（对本选手无效
——交互进程读前端选项环境；徒增用户手写 nitpick 命令的行为差异）。三条禁令：
**不设 `overlord`**（无视 config 强制外置路径 = 拔掉唯一路径，已在钉死清单）；
**不显式选 `*_JNI` 求解器**（原生段错误会击杀整个 PIDE JVM；默认 SAT4J 纯
Java，爆炸半径为零）；已知 Scala 侧取消是协作式的（卡住的求解线程等自身
Event_Timer 到点，有界非即时）。

**裁决映射**：`genuine` → `SOME Refuted`（模型式反驳与 Proved 在融洽理论中
互斥，无需赛后降级）；`quasi_genuine`（不采信）、`potential`（实测会误驳）、
`none`（**零证据**，可在假命题上 50ms 产出）、`unknown`/超时/异常 → NONE。

**静默性**（评审 12）：Auto_Try 按构造静默——全部消息缓冲进返回值第二分量
（nitpick.ML:213-223, :935）；唯一泄漏是 nitpick_hol.ML:1902 一处裸 warning。
诊断需要时把第二分量交给门控 warning 通道。~~Output 拦截~~（进程全局 ref，删）。

### 2.4 R-nunchaku（异步，前置条件齐备后按选手接口插入）

前置：① fork + 组件落地（master d23a876 + cvc5 ≥1.3.1 + wrapper 重指
NUNCHAKU_HOME；独立工程计划）；② `run_chaku_on_prop` 对含 Var 目标的行为
**未探测**，上线前补深查级探针；③ nunchaku.ML 有把不可靠翻译 SAT 误标 genuine
的路径，须加护栏后才可采信；④ bash_process 环境。规格：`solvers = "cvc5 smbc"`
（kodkod 后端零胜场，弃）；SAT genuine → `SOME Refuted`；UNSAT 无证明重构 →
NONE（defer 机制就位后可升级为高置信推迟信号）。ML 层 Nunchaku 结构已在
PLPR 作用域内（Main → Nunchaku → Nitpick），无需动 imports（评审 15，
T 步的可达性分支删除）。

## 3 · 异常与并发纪律（评审 blocker 2）

- **照经验在 PLPR 内小心重写，不抽共享**（作者裁定 2026-08-24）：
  auto_sledgehammer 的成品（`run_branch` :1731-1750、`classify`/`normalise`
  :546-581）经查**无法直接引用**（局部闭包 + 模块私有 + 绑定其失败词汇表），
  抽通用内核则需顺手重构一段正处于 proof store 重录主路径上的生产关键代码
  ——为 ~20 行消重不值。故在 PLPR 里按同一纪律重写一份小的，两处致命坑
  必须逐条落实：① 引擎用"取消"表示"别人赢了"，在分支**内部**把它转成
  失败即灾难——异常处置只装在选手出口；② `Par_Exn` 是容器不是失败，容器
  自身 `Exn.is_interrupt` 为 false、中断变体可藏于其中，调用方必须拆包逐件判。
  配套三条：(a) **双向互指注释**——PLPR 实现处注明孪生在
  sledgehammer_solver.ML:546-581，彼处 `normalise` 旁补一行反向指针（该文件
  唯一改动，纯注释）；(b) T3 增加**取消行为探针**（竞速中发中断：输家停、
  外部进程死、中断穿透到顶，两层坑各有用例）；(c) 三次法则——出现第三个
  消费者（R-nunchaku 外壳 / LLM judge 同步档）时再抽共享内核。
- 单选手层用 interrupt 透明的 `try`（basics.ML:109-110）+ 显式
  `handle Timeout.TIMEOUT => NONE`；**规格明文禁止 `handle _`**——竞速短路
  机制本质是给输家发中断（par_list → future 取消链），吞掉中断 = 输家烧满
  预算 + Ctrl-C/PIDE 取消失效。
- 外部进程的中断击杀链（bash_process 按 uuid server_kill）已核实成立。

## 4 · 不触碰的路径

开头 30ms 串行速证；`is_F` 分支；`safe_obligation_solver`；`fail` 文字。

## 5 · 可靠性论证

1. `Refuted` 只导致跳过规则，永不损害可靠性（风险仅完备性）。
2. `Proved` 只来自 P-auto 的真实定理。
3. R-nitpick genuine 要求模型令 H 真 → 对空虚可证守卫免疫；R-conv 的空虚-H
   缺陷由赛后备胎结构性关闭（§2.2）。
4. **残余非确定性**（原 D12，收缩后如实记录）：仅剩"由哪个反驳选手驳倒"
   （下游同效，无分岔）。混合仲裁规则记录在案：先完成者靠取消令对手来不及
   产出；同时完成者按选手表顺序。

## 6 · 性能与环境

- 墙钟 ≈ max(单路) + 收尾（输家中断/解栈/杀外部进程不免费）；前提
  `max_threads > 1`，否则自动走 `get_first` 短路串行（§1.1）；
  `parallel_limit` 被设为正数的环境会引入负载相关降级，记录在案。
- Kodkod 单路径（评审 11 + 双路径实测 + 作者裁定，取代 rev 2 双路径矩阵与
  中期的"回落"设想）：R-nitpick 恒走 Scala 路径（§2.3），无对端环境安全缺席。
  前端差异是**已量化并文档化的不对称**：PIDE/build ~100ms 级命中；Isa-REPL
  无此选手（现状水平）。T4 探针相应简化：逐前端一次 Scala 对端可用性 + 一次
  真实 R-nitpick 调用；bash_process 探针只为将来的 R-nunchaku 保留（真外部
  二进制）。预算含义：**500ms 即充裕**（作者原值，10/10 命中余量过半），
  700ms 的上调理由随外置路径弃用而消失，T5 实测回填终值。
- kodkod 全局**单槽**结果缓存（debug/overlord 才旁路）：并发下命中率≈0，
  偶中会成为 T5 计时离群点——测量记录其命中数（评审 14）。

## 7 · 实施步骤

- **T0（先于一切实现，决定架构是否值得建——评审 major 5）** 离线命中率实验：
  开 `\<phi>trace_reasoning ≥ 1`（fail 出口默认静默，不开拿不到语料）跑安全前沿
  （至 `Phi_Type.thy`）收集真实守卫；离线对语料跑 Nitpick，报四个数：
  ① genuine 率；② 命中墙钟分布（回填预算默认值）；③ 固有 TVar 占比（结论
  变量携带 schematic 类型的守卫比例；仅作期望校准，无裁决功能——原签④已撤销）；
  ④ 探索性变体"⋀-参数代成固定 Free 绕开 Skolem 化"的产出上限
  ——**只测不上线**（它把可靠反驳弱化为存在反驳）。顺带量 P-auto 在假守卫上
  的失败耗时分布（§2.2 代价记账）。
- **T1** 竞速框架：`race_result`、共享目标项预计算、选手表、`Future.relevant`
  自动降级、§3 异常纪律（复用/抽取 auto_sledgehammer 外壳）、P-auto、R-conv
  （赛后备胎）；删除旧级联 + `ORELSE0` + `Unsupported` 分支；**重命名
  `prove_or_rebute` → `prove_or_refute`**（作者 2026-08-24 指示，修正拼写；
  连同警告文 "falisfy" → "falsify" 一并修正，作者可否决后者）。
- **T2** R-nitpick 选手（§2.3 全部纪律 + §1.2 预算算术）。
- **T3** 探针（imports `Phi_Logic_Programming_Reasoner.PLPR`）：
  ① 地面假守卫被驳、全场短路；② 30–250ms 可证守卫 P-auto 胜出、墙钟不高于
  现状；③ 空虚-H 守卫必须不被 R-conv 抢杀、通常 Proved；④ can_inst=true 仅某
  实例化可证 → 不被误杀，对照全实例皆假 → 被驳；⑤ 含 TVar → R-nitpick 静默
  跳过不吃预算；⑥ `nitpick_params` 污染免疫探针；⑦ 串行（降级路径）与并行
  裁决一致。
- **T4** 前端探针：jEdit / Isabelle-MCP / Isa-REPL 各一次 Scala 对端可用性
  （可用性守卫的实测）+ 一次真实 R-nitpick 调用；确认 REPL 下选手安全缺席。
- **T5** 性能测量：安全前沿墙钟对比 + 插桩（竞速触发次数 / 各选手胜场 / 超时率 /
  是否真并行 / kodkod 缓存命中），回填预算默认值。
- **T6** R-nunchaku（异步等 §2.4 前置①–④，前置工程另立计划）。
- **T7** 文档：PLPR.thy 守卫说明段补竞速结局；本计划补实施日志。

依赖：T0 → T1 → T2 → T3 → T4 → T5 → T7；T6 异步。

## 8 · 决策记录

已定：
- 竞速架构（作者，原 D10）；插入点级联方案作废（原 D1）。
- **子目标升格为一等选手**（作者 2026-08-24 批准）：选手表 =
  `P_auto :: R_conv :: map R_nitpick subgoals`，各拿全预算，并发封顶。
- 预算 Config 保留为参数（作者 2026-08-24 确认）；重命名
  `prove_or_rebute → prove_or_refute`（作者指示）。
- **无总开关、完全替换**（作者 2026-08-23 明确纠正：开关系我方擅自引入、从未
  获批；原 D2 与评审签① 随之消解；单线程降级改为自动判定，非配置）。
- R-conv 赛后备胎（作者裁定，取代 H-可满足性检查与旗标闸门两案；原 D11 关闭）。
- `quasi_genuine`/`potential`/`none` 不采信（原 D5 + 实测铁律）。
- T2 可达性分支删除（评审 15）；`ORELSE0` 删除（评审 13）。

已定（续）：
- 原签③（Kodkod 双路径矩阵删除）被作者的**单路径裁定**连带解决，无剩余分支。
- **原签④ 整体撤销**（作者 2026-08-24 批准三条修正）：其前提——"R-nitpick 在
  can_inst=true 时需先 `Variable.export` 解冻"——经作者质询证实为误设
  （fix_level=1 只冻结假设侧变量，结论变量原样保持 schematic，L976/L1025 的
  正向证明因此无需 export 即可实例化）。修正后 R-nitpick **零变换、原样传入**
  （§2.3），"export vs 不 export"的二选一不复存在；固有 TVar（结论变量携带
  schematic 类型）出现时跳过，无可选择。

已定（2026-08-24 对抗代码评审后，作者逐项裁决，详见 §12）：
- **D1**：外层看门狗 = 预算、统一包裹，直接掐 Nitpick 收尾；§1.2 规则 3/5 已改写。
- **D2**：竞速区按模块级分解重写（race engine / racers / guard solver 三层），
  分节注释遵循手册层级（`Doc/Implementation/ML.thy:76-85`：星号越多范围越大，
  `(**** chapter ****)` > `(*** section ***)` > `(** subsection **)`）。
- **D3**：废除内存计数器（`guard_race_stats`/`count_race` 连 signature 导出一并
  删除），改 `\<phi>guard_race_log` 门控的 TSV 日志文件；§10.3 已改写。
- **D4**：并发封顶条款整条废除（§1.1 已改写；该条款从未经作者单独裁决）。
- **D5**：config 改名 `Phi_Reasoner_guard_race_timeout` → `\<phi>guard_race_timeout`
  （全仓库 28 个 config 中 23 个用 `\<phi>` 前缀，原名是唯一 `Phi_` 拼写孤例）。
- 评审否决、不再重提：deadline 式共享预算（破坏 §1.1 串行/并行裁决一致性）；
  "R-conv 无条件抢答"（会在空虚-H 守卫上把"通过"翻成"跳过"）；绕过 Nitpick
  模型重构（`codatatypes_ok` 参与 genuine 判定，不可绕）。
- 挂起待 T5 实测再议：30ms 前置与 P-auto 判据统一（会剧增竞速触发频率）。

已定（2026-08-25，第二轮对抗评审后作者逐项裁决）：
- **关切一（两处调用线程裸跑代码加护罩）批准**：日志写入经局部辅助
  `checked_io`（`Exn.capture_body` + `contains_interrupt` 重抛 + 否则 `diag 2`）
  保护，`Path.explode` 提至臂顶、每场解析一次、失败即禁用本场日志；预计算
  半边由 D6 结构性解决，无需单独护罩。
- **D6 批准**：R-conv 预计算移入选手体内，选手无条件在场；`r_conv_racer`
  返回 `racer`（非 option），`map_filter I` 消失；原"急切性决定选手表长度"
  辩护注释删除（该耦合被认定为偶然而非收益）。代价记账：非 Trueprop 守卫
  多付一次空 fork（罕见）；选手表恒两元使 forked 列变常量——与 D7 联动。
- **`pauto_finished` 旗标批准（原挂起项，作者提前裁决并亲自补全为对称协议）**：
  两个每场 `Synchronized` 旗标互为镜像——R-conv 找到反驳：先置
  `rconv_refuted`、再读 `pauto_finished`，置位则 `SOME Refuted` 终场，否则照旧
  只记录；P-auto 空手而归（正常跑完无果，超时/崩溃不置位）：先置
  `pauto_finished`、再读 `rconv_refuted`，置位则转发 `SOME Refuted`。
  **"先写自己、再读对方"的顺序承重**（store-then-load：两事件都发生时至少
  一方必见对方，保证早终场；写反则存在双双扑空的交错）。裁决与赛终读记录
  逐字相同，纯提前时序；不变式按构造保持。T1 收益≈0，T2（多选手）收益真实。
- **`Refuted` 携带反驳者名**（`datatype race_result = Proved of thm |
  Refuted of string`；记录变量升级 `string option` 存反驳者名）：P-auto 转发
  时归名指向真正的反驳者，日志/摘要一律 `"refuted by " ^ 反驳者名`；顺带
  单源化 "R-conv" 字面量（评审 B5 的归宿）。
- **`recording_racer` 组合子否决**：其 `unit -> bool` 体类型在类型上禁止获胜，
  与已批准的 pauto_finished（R-conv 条件合法获胜）不相容。
- **自造竞速引擎批准（原挂起项转正）**：落地
  `contrib/Performant_Isabelle_ML/library/race.ML`（signature-first，结构名
  Race；每选手出口报告 Won/Gave_None/Timed_Out/Crashed/Cancelled、全模式真
  短路、join 屏障、诚实模式报告；相关性判定只做一次、无二次降级；无并发
  封顶承 D4）。由 agent 编写 + 两轮对抗评审迭代至无 blocker/major；根理论
  `ML_file` 注册与 PLPR 集成均待引擎过审后另行请示作者。注：`Par_List.get_some`
  的退化窗口经实测在作者环境不可达（`parallel_limit` 默认 0 且全仓库无人设置），
  引擎的价值在真短路语义保证 + 每选手出口数据（服务 D7 的 exits 列）。
  **已完工（2026-08-25）**：`race.ML` 342 行落地并通过完整迭代（编写→两轮
  对抗评审→按合并工单重写→双 ACCEPT 验收→文档收尾）；14 项测试电池
  （含平局不变式、取消路径 join 屏障、脱工人线程调用、确定性 Discarded、
  内部中断隔离）多轮全绿。终版语义：模式一次判定如实报告；先到认领胜出、
  并发认领取最小下标；单选手组 + 永不取消的父组作外部取消探针；六种出口
  `Won/Gave_None/Timed_Out/Crashed/Cancelled/Discarded of 'a`，认领记录是
  胜负唯一权威；选手体浮出中断三臂归因（本组已取消/调用线程被吸收的外部
  取消/选手内部）；全路径 join 屏障；三条不可约残差成文。待作者：注册
  `ML_file` 行 + SKILL/Readme 措辞、race.ML 提交、PLPR 换用引擎的集成时机、
  `contains_interrupt` 三处合一的后续（删 reasoners.ML 副本需 PLPR ROOT 加
  sessions）、测试理论从 scratchpad 迁入仓库（暂 parked）。

已定（2026-08-25 晚，作者指示"更新计划以及代码"）：
- **PLPR 换用竞速引擎立即落地**（不等 T2）：`(** race engine **)` 小节整体
  删除（`run_racer`/`run_race`/本地 `contains_interrupt`/`type racer`），
  由 `Race.race` 接管；已批的 D6、pauto_finished 对称协议、`Refuted of string`、
  关切一护罩（`checked_io` + 臂顶解析日志路径）在同一次重写中一并落地；
  关切三的内容（`p_auto_racer` 入 Racers 小节、`search_solved` 共享判据、
  居首契约注释）与关切四的代码侧杂项（小节标题大写、ctxt/ctxt0 方向注释、
  import/export 分支强弱注释、signature 虚拟时间/墙钟句）随重写自然落地。
- 注册与接线（文件编辑已做，提交另请示）：`Performant_Isabelle_ML.thy` 加
  `ML_file race.ML`；Readme/SKILL 首句放宽为 "data structures and concurrency
  utilities" + Race 条目；PLPR ROOT sessions 加 `Performant_Isabelle_ML`；
  PLPR.thy imports 加 `Performant_Isabelle_ML.Performant_Isabelle_ML`。
  **heap 后果**：Performant_Isabelle_ML → Auto_Sledgehammer → Minilang →
  Minilang_AoA → Phi_System_Base 全链失效，验证前需作者跑/授权一次 build。
- 集成后立即再跑一轮对抗代码评审（作者指示）。

已定（2026-08-25 深夜，集成后评审收口，作者三连批准：修复方案 / build 授权 /
提交）：
- 集成评审终榜（Opus 5 两轮 + 交叉互驳）：正确性与并发本体零 blocker 零
  major；唯一 major 是文档三副本失同步（`.claude/skills/` 下 harness 真正加载
  的那份漏更）。互驳战果：双旗标"依赖硬件内存序"的质疑被四步互斥反证驳倒
  （`Synchronized.value` 同样上锁，协议无条件正确）；重复构造搜索器的性能
  论证被驳倒（`addss` 在闭包内按次求值，属小常数）。
- 修复全部落地：三份模块文档逐字节同步（description 行放宽、Race 条目改准
  "最小下标胜、先到者终局" + Warning 子条目）；节头三句改准（胜负规则/中断
  三臂归因/孪生同步句恢复）；协议注释本质先行 + 收益≈0 注记 + 丢记录残差句；
  "vacuous-hypothesis race"→guard；崩溃不置旗标改结构性理由；**R1 落地：双
  旗标并成单 `Synchronized.var`（`{pauto_finished, refuted_by}` 记录），每选手
  单临界区内"发布自己 + 读对方"，时序论证整段删除**；`r_conv_racer` 收
  `search` 参数（删重复构造）；`negation` 迁回使用点旁；装配点注明引擎两义务。
  评审否决且未做：给选手尾部加不可中断护罩（纪律属引擎边界内）。
- build 已执行（作者授权）：仅 `Phi_System_Base` 需重建（57s），上游链经
  干跑核验新鲜。验证全绿：冒烟三路（control 5ms 不进竞速 / undecided 511ms /
  赛后记录 500ms，TSV 行齐全）；全前沿至 `Phi_Type.thy:8203` 零错误，
  `Phi_Type.thy` 警告行与基线逐行一致，`PLPR.thy` 警告行整体 +1（imports 多
  一行所致，同组警告逐条对应）。
- 遗留小事：auto_sledgehammer 侧孪生注释重指向另行请示（注意其 :1829 递归
  拆包与引擎单层语义不同，不能直接替换调用）。`PLPR.unicode.thy` 作者裁定
  **完全不用管**（2026-08-25）。

已定（2026-08-25 午后，作者指示"请推进 D7, D8"）：
- **D7 落地**：TSV 改为七字段 schema（见 §10.3 修订文——verdict/winner 拆列、
  逐选手出口列、mode 沿用引擎如实报告、选手数列删除）；signature 注释同步。
- **D8 落地**：本计划迁入 `contrib/phi-system/Docs/`（与引用它的源码同仓；
  jedit/*_PLAN.md 先例），reasoners.ML 两处引用改 `Docs/` 路径；主仓库中
  删除原件。

- **SPIN/BAD 构造件迁库（作者 2026-08-25 赞同方案一）**：冒烟理论落成
  `Phi_Logic_Programming_Reasoner/Test/Guard_Race_Smoke.thy`（不注册 ROOT，
  按需经 MCP 评估）；日志路径改 `$ISABELLE_TMP_PREFIX/guard_race_smoke.tsv`；
  测试升级为**断言式**（对每场竞速新增日志行的 (verdict, winner) 列断言，
  失配即 error 跑红）；`\<^context>` 静态反引与 BAD 居首两条教训注释在文件内。
  三路实测全绿。T3 在此文件上扩建七探针。scratchpad 的 T0_Smoke.thy 就此退役。
- D7/D8 改动已提交（phi-system ae1dd806，主仓库 a5b0ae7）。
- 日志设施定位经作者确认（2026-08-25）：**常驻但默认关死**——纯测量用途、
  生产零开销、不删除；T5 及将来任何再测量直接开 config 使用。

已定（2026-08-25，作者批准 #1）——**N1 裁定：R-conv 冻结分支改用导入语境**：
- 裁定内容：can_inst=true 分支不再丢弃 `Variable.import` 产出的导入语境
  ctxt'，而是在选手体内以 `auto_search_tac ctxt'` 就地重建搜索；
  can_inst=false 分支、P-auto 与 30ms 快攻照旧共享外层 `search`。
  原则一句话：**每条分支的搜索运行在其目标所生活的语境下**。
- 记录的理由（对抗辩论合流结论，两位裁判一致；引错依据视为记录性错误）：
  守卫竞速运行在**下游用户的证明语境**上（`\<phi>reasoner_ML` 注册 +
  五个直接调用点，wrap 透传推理引擎实时 ctxt），用户理论可经
  `Classical.addSWrapper` 等正规扩展点注册 wrapper 进入搜索链，任何
  phi-system 侧 grep/注释都够不着；账本正确的语境是对"写得对的 wrapper"
  的最低承诺。理由**不是**防错误判定（内核在已探测路径上两案同样挡得住，
  PC2），**不是**惯例一致（两树均无"只吃布尔仍留语境"的严格同型先例；
  Quickcheck.test_goal 是最近旁证），**不是**发现 R（跨场同名铸造两案
  等价，双方共同划掉）。
- 研究档案：三研究员（源码追踪 F1–F9 / 对抗实测 13 探针含 PC0-PC2 /
  惯例普查 ~20 保留 vs 4 丢弃）+ 两裁判两回合辩论，辩护现状方依预承诺
  倒戈条件转向；其核验另发现竞速语境本装有 phi 注册的
  guess_inst_solver（simp solver，落在 F3 已证无害形状）。探针理论
  scratchpad T2_Context_Probe.thy / T2B_Adversarial_Probe.thy。
- 辩论副产物立案（T2 期单独呈作者裁决）：`search_solved` 验收谓词只查
  `Thm.no_prems`、不查 hyps/tpairs——双方唯一都认可的潜在判定翻转路径，
  与语境选择无关；加固形状为 Goal.conclude 级检查，覆盖两分支与 P-auto。
- §11.1 ④ N1 备忘就此关案；代码注释同步改写（错误理由不得写入）。

（Guard_Race_Smoke.thy 已获批提交：phi-system 4609815a，2026-08-25。）

已定（2026-08-25，作者"1–5 全批"）：
- **#2 裁定**：R-nitpick 假设收集喂**目标侧语境 ctxt**（`Assumption.all_assms_of
  ctxt`）——Nitpick 官方入口同款（nitpick.ML:984-996）；实测该假设集对
  ctxt0/ctxt 选择不敏感（前处理只登记变量不产生假设），取"目标在哪问哪"
  为定论。
- **N1 落地并验证**：r_conv_racer can_inst=true 分支改为绑住 ctxt'、体内
  `auto_search_tac ctxt'` 重建搜索；专项探针 N1_TrueBranch_Probe.thy
  （scratchpad）两测全绿——空冻结与真冻结（?x→x_）均由 R-conv 正确反驳。
  探针途中实测到两条**可达性补遗**：等式形守卫（?x = t）被 fast_inst
  平凡形通道先行拦截；simp 可判的带变量原子（?x < 0）被竞速前置的
  asm_full_simp+quick_cut 廉价判死——两者都到不了竞速，探针必须用
  simp 不可见的带变量原子（BADP 构造件）。
- **T2 落地（§2.3 全部纪律）**：reasoners.ML 新增 kodkod_peer 懒探测
  （`can \<^scala>\<open>echo\<close>`，无对端则选手缺席）、is_fixed_equation/
  extract_fixed_frees 照抄件（Nitpick 未导出，注明出处）、nitpick_params
  钉死清单（§2.3 各键 + falsify=true 防 satisfy 污染 + card 钉回官方默认
  "1-10"；timeout=预算十进制秒串；tac_timeout=0.05）、r_nitpick_racer
  （零变换传目标、subst 真传、Auto_Try 静默、只信 genuine）、装配点
  （TVar 筛除：假设含 ?'t 则全体缺席、子目标含 ?'t 则该选手缺席；
  选手表 P_auto :: R_conv :: R-nitpick*）。
- **T2 验证（冒烟扩至四测，全绿）**：BAD∧SPIN 由 R-nitpick1 **86ms 直接
  终场**，P-auto 出口 timeout→cancelled（早终场收益首次实测可见）；
  断言助手升级为备选集（两名正确反驳者之间的时序竞速，两种日志都合法）；
  新增 BADN 测试（无任何规则的假原子，经典反驳者不可见、仅 Nitpick 能驳，
  102ms 胜出）；搜索炸弹仍 undecided 且实测澄清：read_prop 把 'a 读成
  固定 TFree，R-nitpick 在场并按全称读法正确空手（exits：R-nitpick1:none）
  ——schematic ?'a 屏蔽的专项探针留给 T3。前沿警告基线逐行不变。

待作者裁决：本轮改动（N1 + T2 + 冒烟扩建 + 计划誊记）的提交。

## 9 · 档案索引

- 对抗评审（2026-08-23，两轮，Opus 5 双评审员）：15 条终榜（2 blocker、9 major、
  4 minor，零否决），全部已吸收进上文；报告全文见会话记录。评审独立复核确认：
  `close_form` 语义读法、两入口一致性、假设侧独立闭包只漏驳不误驳（原 M8）。
- 文献调研、Nitpick/Nunchaku 基准（57+21 目标，速度画像、真包含告破、
  "none 零证据"铁律）、Nitpick schematic 深查（30+ 例矩阵）、Nunchaku 复活
  实证：见 rev 2 档案（会话记录）与 scratchpad `results*.tsv`。关键铁律不变：
  只信 genuine；none 是零证据；Nunchaku UNSAT 无 thm 不能当证出。

## 10 · 执行交接（2026-08-24，为 compaction 准备；本节假定读者没有会话记忆）

### 10.1 状态一句话

设计全部定稿（§8 已定清单即全部作者裁决），无任何待裁决设计项；作者指示
compact 后开工。唯一待作者澄清：开工起点是 T0（离线命中率实验，计划序）还是
直接 T1（作者原话"开工写代码"，若答"直接 T1"则 T0 的四个测量并入 T5 事后补）。

### 10.2 T0 详细作业（若从 T0 开始）

目的：在真实守卫上量 R-nitpick 的价值与预算，四个数：① genuine 率；② 命中
墙钟分布；③ 固有 TVar 占比；④ "⋀-参数代固定 Free"变体上限（只测不上线）。

做法（单次评估、就地测量，避免二次解析 dump）：
1. **临时插桩**（跑完即 revert，勿提交）：在 reasoners.ML 的 `fail` 出口
   （:980 附近）加一个探针调用：对每个到达此处的守卫 goal 记录——goal 的
   `YXML`/字符串、can_inst、`Term.add_tvars` 是否非空（③）；随即在同一
   ctxt 里按 §2.3 全套规格调一次 Nitpick（含 `Config.put Kodkod.kodkod_scala
   true`、参数钉死清单、1s 超时、通吃兜底），记录裁决与 `Timing.timing`
   墙钟（①②）；再跑一次变体④（把 ⋀-参数经 `Logic.goal_params` 代成固定
   Free 后同样调用）。结果以行式追加写入 scratchpad 下一个 TSV（用
   `File.append` + serial，防并发写花）。同时记录 P-auto 风格的失败耗时：
   对同一 goal 跑 `Timeout.apply 1s auto_search_tac` 记墙钟（§2.2 代价账）。
2. **跑语料**：重启 REPL 无关——用 isabelle-mcp `isabelle_launch` session
   `Phi_System_Base`（该 heap 只含外部依赖，phi-system 源码含插桩后的
   reasoners.ML 会从源码加载），`isabelle_evaluate_to` 到
   `contrib/phi-system/Phi_System/Phi_Type.thy` 末行（2026-08-21 的绿色安全
   前沿，约 13 分钟）。轮询 `isabelle_evaluation_status` 至完成。
3. **收数、revert 插桩、汇总**：TSV 聚合出四个数 + P-auto 失败耗时分布；
   回填 §1.2 预算与 §2.3 期望校准；把数字写进本计划新增小节。
4. 注意：插桩会拖慢评估（每个无果守卫 +≤2s），属预期；`\<phi>trace_reasoning`
   无需开启（探针直接写文件，不走 warning 通道）。

### 10.3 T1 详细作业（竞速框架）

**改动文件**：`Phi_Logic_Programming_Reasoner/library/reasoners.ML`（主体）、
`library/helpers0.ML`（删 ORELSE0）、auto_sledgehammer 的
`sledgehammer_solver.ML`（仅 `normalise` 旁加一行孪生指针注释）。

**动工前置检查（必须先做，结果写注释）**：读 `Pure/Concurrent/par_list.ML`
与 `future.ML` 的 `forked_results`，确认"`Par_List.get_some` 在无人返回 SOME
的路径上 join 全部选手后才返回"——这是 R-conv 赛后记录可见性的同步屏障。
不成立则赛后备胎设计需回炉，先停手报作者。

**实现顺序**：
1. `datatype race_result = Proved of thm | Refuted`；
2. 选手异常纪律（§3：孪生重写）：每选手出口 = interrupt 透明 `try` + 显式
   `handle Timeout.TIMEOUT => NONE`；竞速调用方接住重抛异常时拆 `Par_Exn`
   容器逐件判中断（两条坑的注释 + 指向 sledgehammer_solver.ML:546-581）；
   **禁 `handle _`**；
3. 共享预计算：子目标列表（`Thm.cprems_of`）+ 各选手所需形态一次算好
   （R-nitpick 原样零变换，§2.3；R-conv 沿用现 conv_goal + import/export）；
4. 选手表 `P_auto :: R_conv rconv_refuted :: map R_nitpick subgoals`；
   `run = if Future.relevant racers then Par_List.get_some else get_first`；
   并发封顶信号量（按 `Multithreading.max_threads`）；
5. P-auto：`Timeout.apply budget (auto_search_tac ctxt)`，全解 → Proved；
   R-conv：证出否定目标 → `Synchronized.change rconv_refuted (K true)`、
   返回 NONE（**用 `Synchronized.change`，勿用 `assign`**——assign 置
   Immutable 后 guarded_access 会 Fail；本设计只 `change`+`value`，无等待）；
6. 结果分派（§1.1 骨架）：SOME Proved → Seq.single；SOME Refuted →
   Seq.empty；NONE → 查 rconv_refuted → true 则 Seq.empty，否则 fail；
7. 删除：旧链 :1023-1032（含 `Falsified`、`Unsupported` 分支）、
   `helpers0.ML:514-519`（ORELSE0 连声明）；保留 :976 的 30ms 前置速证、
   is_F 分支、`timed_tac`/`timed_seq`（is_F 分支仍用）；
8. 重命名 `prove_or_rebute → prove_or_refute`（全部调用点 grep 确认仅
   guard_condition_solver :1059 一处）+ 警告文 "falisfy"→"falsify"；
9. 配置：`Phi_Reasoner_guard_race_timeout` int Config，默认 500，在
   PLPR.thy 现有 config 声明区（:1955 附近）注册 attribute。

**诊断分级**（输出一律 `warning`，禁 `tracing`；门 = 现有
`\<phi>trace_reasoning`，默认 0 全静默）：
- level 1：现有 fail 文字原样（typo 修正后）；
- level 2：每场竞速一行摘要（胜者/墙钟/子目标数/是否真并行）+ 被兜底吞掉
  的非中断异常原文（防"静默失效无人知"）；
- level 3：R-nitpick 每子目标明细（裁决/耗时/TVar 跳过）+ Nitpick 返回值
  第二分量的消息。
定量测量走**日志文件**（作者裁定 2026-08-24，取代原"进程内 `Synchronized.var`
计数器"设计；字段清单经 D7 修订，作者 2026-08-25 批准推进）：config
`\<phi>guard_race_log`（字符串，默认空 = 不记，生产零开销）；非空时每场竞速
结束、裁决已定后 `File.append` 一行 TSV，七个字段：**流水号、verdict 单词
（proved/refuted/undecided）、winner 选手名或 "-"、墙钟毫秒、子目标数、mode
（forked/serial）、逐选手出口**（`名:码` 逗号串，码域
win/none/timeout/crash/cancelled/discarded，直接映射自引擎 exits）。直接获胜
与赛后记录共用 verdict=refuted，由出口列区分（记录路径无 "win" 出口）；选手
数从出口列可导出故不设列；超时率从出口列可得（D7 的立项动机）。组装在结局
分派总映射内。仍然禁止解析警告文字。

### 10.4 T2 之后

按 §7 序：T2 R-nitpick（§2.3 全部纪律逐条落实，尤其参数钉死清单与
`def_assm_ts=[]`）→ T3 七个探针 + 取消行为探针（§3(b)）→ T4 前端探针 →
T5 性能测量 → T7 文档。T6（R-nunchaku）异步等前置，其 fork 工程另立计划。

### 10.5 环境与纪律（承 CLAUDE.md 与既有裁决）

- **绝不 `isabelle build`**（除 repl_server.sh）；改 `.ML` 后重启 REPL 即生效；
  PIDE 验证用 isabelle-mcp `Phi_System_Base`（其余 heap 会把 PLPR 预编译进去
  导致改动不可见）。
- 共享工作目录：不 stash/checkout/reset --hard/clean；直接在 main 提交，但
  **提交须作者逐次明示批准**。
- scratchpad（本会话）：`/tmp/claude-1002/-home-qiyuan-Current-MLML/966ef49e-…/scratchpad`
  存有历次基准数据（`results*.tsv`、`bench*.ML`、Kodkod 双路径探针等）。
- 代码完成后跑**统一对抗代码评审**（作者已定），任务书点名攻击三个 delta：
  R-conv 赛后备胎的同步语义、as-is 变量纪律的量词论证、Scala 单路径集成
  （守卫位置 / Config 穿透 / 协作式取消残留）。
- 用户 jEdit prover（pid 535507 等）绝不可杀；杀进程类操作前必须核实身份。

## 11 · 实施日志

### 11.1 T0 + T1（2026-08-24，作者指示"T0 T1 一起写"）

**动工前置检查通过**：`Par_List.get_some` 无人胜出路径先经 `managed_results ->
Future.forked_results -> join_results`（future.ML:530-541，等全部 future 完成后才
`map get_result`），随后才扫描结果——R-conv 赛后记录的写入先于读取，同步屏障成立。
另核实 `Par_Exn` 不变式只排除 proper interrupt：`Exn.Interrupt_Breakdown` 不属
proper、**可以**藏进容器（容器自身 `is_interrupt` 为 false）——调用方必须拆包逐件
判中断（孪生 sledgehammer_solver.ML 的注释早已写明此坑；实现照做）。

**T0 结果（重要）**：
1. **可达性发现**：`auto_search_tac` 是 TRY 链，除非 30ms 超时否则**总会**至少产出
   原状态——`ORELSE` 因此永不落空。旧级联（falsify + fail 出口）与新竞速的**唯一
   入口是"30ms 速证超时"**。30ms 内返回部分进展状态的守卫被外层 `SOLVED'` 静默
   丢弃（即档案里"第四种无声结局"的真实主体），级联/竞速根本看不到它们。
2. **语料零命中**：探针插在 fail 出口，跑完整个安全前沿（PLPR -> Phi_Type.thy，
   绿色）**一次都没触发**——该语料上不存在"30ms 超时且级联无果"的守卫。T0 的
   四个数在此语料上空洞；并入 T5 换更丰富语料（Phi_Examples / 实际 IDE-CP 会话）
   事后补。
3. 合成守卫单点数据（Andrews 挑战式，真命题）：Nitpick as-is `none` 226ms、
   开 \<And>-参数变体 `none` 115ms、P-auto 1s 烧满超时。探针代码存档于会话
   scratchpad `t0_probe_block.ML`（注意 2025-2 无 `YXML.content_of`，
   要用 `XML.content_of (YXML.parse_body -)`）。
4. **待作者裁决的新设计问题**：竞速是否也应在"30ms 内返回部分进展但未全解"时
   触发？现计划 §4 保留前置不动（= 这类守卫继续静默死亡）。未实现，仅记录。

**T1 已落地**（三个文件）：
- `reasoners.ML`：竞速实现替换旧级联（§1.1 骨架 + §1.2 预算断言 + §2.1/2.2 选手 +
  §3 异常纪律含 `contains_interrupt` 拆包）；重命名 `prove_or_rebute ->
  prove_or_refute`（唯一调用点 guard_condition_solver）；警告文 "falisfy"->"falsify"；
  新增 `guard_race_timeout`（Config，默认 500ms，attribute
  `Phi_Reasoner_guard_race_timeout`）与 `guard_race_stats`（`int Symtab.table
  Synchronized.var` 事件计数器，进 signature）；诊断走 `Phi_Reasoner.warn_pretty`
  level 2（每场一行：胜者/墙钟/子目标数/是否并行 + 被吞非中断异常原文）。
- `helpers0.ML`：`ORELSE0` 连声明删除。
- auto_sledgehammer `sledgehammer_solver.ML`：`normalise` 注释块加孪生指针一行。

**T1 冒烟（T0_Smoke.thy，均实测通过）**：
- 快速部分进展守卫：5ms 空返回，竞速未进（现状语义保留）；
- 未决守卫（搜索炸弹）：进竞速，undecided 500ms，fail 警告文已是 "falsify"，
  计数器 `race/parallel/undecided +1`；
- 假守卫（SPIN 自旋原子烧前置 + BAD 原子 elim! 秒杀否定）：**R-conv 赛后记录路径
  全程验证**——`refuted (R-conv record) in 500ms`，计数器 `rconv_refute+1`，静默
  跳过（Seq.empty），无 fail 警告。
- P-auto 胜出路径需"30-500ms 窗口内可证"的守卫，留 T3 精配（可用有界 SPIN 链）。
- 冒烟工具沉淀：`SPIN`（intro! 无限上行，只烧目标侧）与 `BAD`（无 simp 规则 +
  elim!）是 T3 探针的可控构造件；注意 ML 块 `\<^context>` 是静态反引，测试辅助
  函数必须由调用点传入语境（否则新声明的规则不可见——踩过）。

**评审修复期补记（2026-08-24，§12.2-16 指定写入）**：
① 旧判据差异：对"30-500ms 窗口内取得部分进展"的守卫，旧级联最多 ≤310ms 即静默
返回部分状态（随后被外层 `SOLVED'` 丢弃），新竞速则烧满预算、并在
`\<phi>trace_reasoning ≥ 1` 时给出 undecided 告警——两者对调用方的**证明结局相同**
（都是该守卫不被解决），差异只在耗时与可见性。
② `Phi_Types.thy`（注意：与 T0 语料前沿终点 `Phi_Type.thy` 是**两个不同 theory**）
是已知 3 命中语料——TODO.md:38 记录其一次运行触发 3 条守卫 fail 警告
（`Phi_System/Phi_Types.thy` :2527/:2581 附近）；T5 以它为目标语料收数。
③ config 声明惯例：`Attrib.setup_config_*` 直接写在 `.ML` 内即完成注册（本仓库
28 个既有 config 皆如此）；§10.3 步骤 9 所写"在 PLPR.thy 注册"系笔误，勿照做。
④ N1 备忘（**T2 进场前的阻塞性检查项**）：R-conv 预计算里
`Variable.import false gs ctxt |> #1 |> #2` 丢弃了导入后的语境、只留下定理，而
`solved1` 用外层 `ctxt` 搜索——此形状是旧级联代码原样继承，T1 刻意未动；T2 实现
§2.3 的 assms/subst 纪律时必须正面回答"该用哪个语境"这一问题。
⑤ §2.2 如实记录：R-conv 赛后记录目前**唯一**可观察效果是抑制一条默认关闭的
level-1 fail 警告——对调用方而言三种失败出口（记录命中 `Seq.empty`、undecided
`fail`、无记录 `Seq.empty`）观察等价（`fail` 序列 pull 时也返回 NONE）；冒烟
验证到的就是这条警告的有无。

环境备注：本日 heap 曾全体缺失（用户 8-23 晚清空 `~/.isabelle/Isabelle2025-2/heaps`
后本地重建失败 rc 127，从 cslh19 拉取系统 heap 压缩包解压恢复），Phi_System_Base
由用户配置好后 MCP 启动正常。

## 12 · 对抗代码评审结果与修复执行交接（2026-08-24；本节假定读者没有会话记忆）

### 12.1 评审档案一句话

两轮对抗评审（Opus 5 双评审员：正确性/并发透镜 + 设计/优雅性透镜；第二轮交叉
互驳、各有撤回与驳倒），零 blocker。并发核心全部对照 Pure 源码核实成立：输家
取消链（future.ML:422-455, 245-258）、赛后记录 happens-before（三种执行模式
皆成立）、`contains_interrupt` 对 `Par_Exn` 不变式的处置、`Exn.capture` 管理
式捕获。作者对全部裁决项的定案见 §8"已定（2026-08-24 …）"。评审报告全文在
会话记录；被否决/降级意见已记 §8，勿重推。

### 12.2 修复执行清单（作者已批准，compact 后照此动工）

目标文件：`contrib/phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML`
（竞速区现约 :976-1170，signature 增补在 :144-152）；另有 `Docs/TODO.md` 与本
计划的文档性修补。全部完成后按 12.3 验证。

**A. 结构重写（D2，其余修复织入其中）**——竞速区重排为：

```
(*** Guard Race ***)

(** race engine **)
  datatype race_result = Proved of thm | Refuted
  type racer = string * (unit -> race_result option)
  fun contains_interrupt exn = ...       (*现 :1117-1121 原文提升*)
  fun run_racer diag budget (name, body) = ...
  fun run_race diag budget (racers: racer list) : (string * race_result) option
      (*内含 Future.relevant 选择 get_some/get_first、计时、外层异常处置*)

(** racers **)
  fun r_conv_racer can_inst ctxt ctxt0 rconv_refuted goals : racer option = ...
      (*conv_goal / conv_goals(import|export 原文) / solved1 全部迁入；
        Unsupported => NONE = 选手缺席*)

(** guard solver **)
  fun prove_or_refute can_inst ctxt ctxt0 = ...   (*§1.1 骨架，约 35 行*)
      racers = ("P-auto", p_auto) :: map_filter I [r_conv_racer ...]
```

分节层级依 `Doc/Implementation/ML.thy:76-85`（星号越多范围越大）。

**B. 逐项修复**（严重度从评审终榜，全部已批）：
1. 两处 `General.exnMessage` → `Runtime.exn_message`（选手崩溃诊断 + 竞速机器
   错误诊断；本文件 :867-868 与孪生 sledgehammer_solver.ML 皆用后者）。
2. 胜者身份穿出：`run_racer` 返回 `(选手名, 结果) option`；摘要文与日志行带名。
3. 预算钳制：`Time.fromMilliseconds (Int.max (1, Config.get ctxt guard_race_timeout))`；
   删除 `Timeout.ignored` 断言与战术内 `error`（§1.2 规则 5 新文）。
4. 外层包裹统一 `Timeout.apply budget`（D1 定案，形状不变，勿加字段）。
5. 结局分派总映射：`outcome → (日志行字段, 摘要词, 返回序列)` 一张表，四分支
   （Proved/Refuted/记录命中/undecided）各给三元组，`fail` 仍是 undecided 的
   返回序列。日志行在此组装（见 7）。
6. 计数器整体删除：`guard_race_stats`、`count_race`、signature 里的导出行；
   冒烟理论 `T0_Smoke.thy`（scratchpad）里读 stats 的部分同步改读日志文件。
7. 日志（D3 定案）：新 config `\<phi>guard_race_log`（`Attrib.setup_config_string`，
   默认 ""）；非空时 `File.append` 一行 TSV：`serial_string()`、裁决（含胜者名）、
   墙钟 ms、选手数、子目标数、并行标志。
8. config 改名（D5）：binding `\<phi>guard_race_timeout`（默认 500 不变），ML 名
   `guard_race_timeout` 保留；signature 导出两个 Config.T（timeout + log）。
9. `diag` 收 thunk（惰性化，恢复 `warn_pretty` 的 `(unit -> Pretty.T)` 设计）。
10. `Timing.start ()` 移到竞速臂顶端（conv 预计算之前）。
11. `contains_interrupt` 在 `run_racer` 出口同样使用（与外层同一谓词；孪生的
    "内层检查不冗余"注释所指即此）。
12. 两处 `Exn.capture (fn () => ...) ()` → `Exn.capture_body`。
13. 诊断诚实化：摘要/日志报"我们选择的模式"（forked/serial），不再断言
    "parallel"（`Par_List.get_some` 内部会二次判定 `Future.relevant` 并可能
    降级为不短路的 map，par_list.ML:31-37——在 `run_race` 的选择处加一行注释
    说明该条件判断因此不冗余，防止后人"化简"）。
14. 注释整饬：可见性证明压成一句 + 指向 §11.1；**保留**空虚-H 三行论证
    （评审裁定承重）；`change`-勿-`assign` 注释随计数器删除只保留在
    `rconv_refuted` 处；孪生指针按名字（classify/normalise）收拢到 section
    头一处；par_list/future 的行号引用改函数名；头注释补一句
    "`Refuted` 在 T2（R-nitpick）之前无生产者"；signature 里 "shared budget"
    措辞改为"每选手预算；串行降级时墙钟上界 = 选手数 × 预算"；conv 预计算处
    加一行：其急切性决定选手表长度进而决定并行/串行（`Future.relevant` 对
    单元素表恒 false）。
15. `Docs/TODO.md` 加转发注：`prove_or_rebute` 已更名 `prove_or_refute`、级联
    已由竞速取代、"falisfy" 已改 "falsify"、30/30/250/100 预算实验不可复现。
16. §11.1 补记（写进本计划）：①旧判据差异——30-500ms 窗口内部分进展的守卫，
    旧级联在 ≤310ms 静默返回部分状态（被 SOLVED' 丢弃），新竞速烧满预算并在
    trace≥1 时告警，证明结局不变；② `Phi_Types.thy`（注意与 T0 语料
    `Phi_Type.thy` 是两个 theory）为已知 3 命中语料（TODO.md:38，
    :2527/:2581 附近），T5 的目标语料；③ config 用 `Attrib.setup_config_*`
    在 .ML 内声明是正确惯例（§10.3 步骤 9 的"在 PLPR.thy 注册"系笔误）；
    ④ N1 备忘：`Variable.import false gs ctxt |> #1 |> #2` 丢弃导入语境而
    `solved1` 用外层语境搜索——旧代码原样继承、T1 未动，T2 实现 §2.3 的
    assms/subst 时必须正面回答此语境问题（阻塞性检查项）；⑤ §2.2 补一句
    如实记录：赛后记录目前唯一可观察效果是抑制一条默认关闭的 level-1 警告
    （三种失败出口对调用方观察等价），冒烟验证的即此。

### 12.3 验证（修复落地后）

1. MCP `Phi_System_Base` 重新评估 scratchpad `T0_Smoke.thy`（先按 6 改其读数
   方式，并给竞速例 declare `\<phi>guard_race_log`）：三路结局 + 日志行字段核对；
2. 全前沿评估至 `Phi_System/Phi_Type.thy` 末行：零错误、警告行与基线一致
   （基线 = §11.1 记录的那组行号）;
3. 改 `.ML` 后 REPL 侧照例只需重启（本轮验证走 MCP，无需 REPL）。

### 12.4 其后顺序

修复收口 → T2（R-nitpick，§2.3 全纪律 + §1.2 新规则 3/5；D1 已定统一包裹；
进场前先答 §12.2-16-④ 的语境问题）→ T3 探针（注意可达性约束：所有探针守卫必须
烧穿 30ms 前置——SPIN（intro! 无限上行，只烧目标侧）/BAD（无 simp 规则 +
elim!）构造件已在 T0_Smoke.thy 沉淀；`\<^context>` 是静态反引，测试辅助函数必须
由调用点传语境）→ T4 前端探针 → T5（用 `\<phi>guard_race_log` 在 `Phi_Types.thy`
收数，回填预算）→ T7 文档。T6 异步不变。

### 12.5 环境与纪律（不变，承 §10.5）

绝不 `isabelle build`；共享工作目录禁 stash/checkout/reset/clean；提交须作者
逐次明示批准；scratchpad 为
`/tmp/claude-1002/-home-qiyuan-Current-MLML/966ef49e-eb27-4d41-b984-25a7eff4cebd/scratchpad`；
用户 jEdit prover 绝不可杀。heap 环境已由用户恢复（系统 heap 自 cslh19 解压），
MCP `Phi_System_Base` 可正常启动。

### 12.6 执行完成记录（2026-08-24）

§12.2 全部落地：A 结构重写（`(*** Guard Race ***)` 下 race engine / racers /
guard solver 三小节；`type racer`、模块级 `contains_interrupt`/`run_racer`/
`run_race`、`r_conv_racer : ... -> racer option`、`map_filter I` 组装选手表；
`negation` 随迁 racers 小节）与 B1–B16 逐项修复均已写入。与蓝图的唯一偏差：
`run_race` 返回 `bool * (string * race_result) option`（首分量 = 实选模式
forked?）而非蓝图的裸 `option`——B13"诊断报实选模式"要求把模式穿出，蓝图两处
本就相互蕴含此形状。结局映射中裁决词兼作日志字段与摘要词（B5 的三元组由此
收敛为二元组，无信息损失）。

§12.3 验证全绿（MCP `Phi_System_Base`）：
- 冒烟三路：control 10ms 不进竞速、无日志行；搜索炸弹
  `undecided in 528ms, 1 subgoal(s), forked` + fail 警告（"falsify"）+ 日志行
  `18083246→undecided→528→2→1→forked`；BAD∧SPIN
  `refuted by R-conv (post-race record) in 500ms` + 日志行、无 fail 警告。
  TSV 字节核对：制表符分隔、行尾换行。
- 全前沿至 `Phi_System/Phi_Type.thy:8203`：零错误；`Phi_Type.thy` 警告行
  （2222, 2633, 5811, 5925, 6074, 6130, 6187, 6290, 6324, 6357, 6379, 6400,
  6604, 6744, 7134, 7174, 7213, 7267, 7365, 7410, 7448, 7718, 7896）与
  `PLPR.thy` 警告行均与 T1 基线逐行一致。

未提交（等作者逐次批准）。下一步照 §12.4：T2 进场，先答 §12.2-16-④ 语境问题。

## 13 · T2 进场交接（2026-08-25，compact 前准备；本节假定读者没有会话记忆）

### 13.1 状态一句话

竞速架构全部落地并提交：竞速引擎 `race.ML`（Performant_Isabelle_ML 仓库
686a067，342 行，独立对抗评审+验收通过）；PLPR 集成（phi-system d0e0869b，
含 D6/对称早终场协议/Refuted 带名/checked_io 护罩/集成评审全部修复——协议
状态是**单个** `Synchronized.var` 记录 `{pauto_finished, refuted_by}`）；
D7 七字段日志 + D8 计划迁库（phi-system ae1dd806，主仓库 a5b0ae7 删原件）。
冒烟理论已迁库为断言式回归测试
`Phi_Logic_Programming_Reasoner/Test/Guard_Race_Smoke.thy`（三路全绿）。
MCP `Phi_System_Base` 正常（heap 2026-08-25 重建）。全前沿零错误、警告基线
逐行核对一致（`PLPR.thy` 组整体 +1 系 imports 增行）。

### 13.2 未决事项

- **Guard_Race_Smoke.thy + 本计划 §8/§13 誊记的提交**：作者批准待发。
- auto_sledgehammer 侧孪生注释重指向 `Race.contains_interrupt`：一句注释，
  另一仓库，须作者点头；注意其 sledgehammer_solver.ML:1829 的**递归**拆包与
  引擎单层语义不同，只能改注释不能直接换调用。
- `Phi_Examples/` 下有**其他 agent** 的未提交改动（约 175 行证明提示删除）
  ——提交任何 phi-system 改动时显式 stage 自己的文件，勿捎带。

### 13.3 T2 第一步：语境探针（阻塞性检查项，§11.1 ④ / 原 §12.2-16-④）

问题重述（假定读者无记忆）：R-conv 预计算的 can_inst=true 分支
`Variable.import false gs ctxt |> #1 |> #2` 把 schematic 冻结成新 Free 后
**只留下定理、丢弃了导入语境**，随后 `search_solved` 用外层 `ctxt` 搜索——
冻结出的 Free 在外层语境未声明。此形状系旧级联原样继承、T1/集成刻意未动。
T2 实现 §2.3 的假设收集（`Assumption.all_assms_of ctxt` 起手 +
`extract_fixed_frees` 的 subst 真传）时必须正面回答"喂哪个语境"，且与
评审记录的姊妹问题一并答：can_inst=false 分支 `Variable.export ctxt ctxt0`
解冻恰好被冻结的变量、给出存在式反驳（§2.3 已裁定接受为完备性弱化——
问题只是两分支语境选择要写成有据的定论）。

探针设计（建议，实施者可按实测修订）：造 can_inst=true、结论带 schematic
变量的守卫（形态参考深查矩阵 case 6，档案见 §9）；在 MCP 下对比 (a) 现状
外层 `ctxt` 与 (b) 导入语境 ctxt'：`Variable.is_declared` 对冻结 Free 的
判定、`search_solved` 行为差异、`Assumption.all_assms_of` 两语境的假设集
差异。纪律：isabelle-mcp 行为必须实测不得从源码推断（既有教训）；探针用
正对照 + 目标之后的可观察副作用。拿测量结果向作者提答案，那是 T2 期第一个
需要作者裁决的时刻。

### 13.4 T2 主体（语境问题答毕后）

照 §2.3 全部纪律逐条落实：变量零变换原样传入、TVar 检出即本选手缺席、
假设与 subst、参数钉死清单（每场竞速构造一次、子目标选手共享）、Kodkod
单路径 + 三行可用性守卫（无 Scala 对端则不进选手表）、只信 genuine、
Auto_Try 静默。选手表 `P_auto :: R_conv :: map R_nitpick subgoals`（每
子目标一选手、各拿全预算；`Timeout.apply` 包裹在装配点统一 map 完成——
引擎调用方义务）。R-nitpick 的 genuine 直接 `SOME (Refuted <选手名>)`
终场，不看协议旗标（模型式反驳与 Proved 在融洽理论互斥，§2.3 裁决映射）；
引擎的 exits 列自动覆盖新选手，日志无需再改。完成后 T3 在
Guard_Race_Smoke.thy 上扩建七探针（§7 T3 清单）。

### 13.5 环境与纪律（承 §10.5/§12.5）

绝不擅自 `isabelle build`；作者已为**验证目的**给出 build 长效授权
（2026-08-25，建议派 agent 执行；仍禁 -c/-f）。改 `.ML` 后 REPL 只需重启、
MCP 自动重同步。共享工作目录禁 stash/checkout/reset/clean。提交须作者
逐次明示批准；推送只 push origin 且须作者吩咐。用户 jEdit prover 绝不可杀。
scratchpad：`/tmp/claude-1002/-home-qiyuan-Current-MLML/966ef49e-eb27-4d41-b984-25a7eff4cebd/scratchpad`
（旧 T0_Smoke.thy 已退役，勿再用）。日志设施常驻默认关（作者确认），
`PLPR.unicode.thy` 完全不用管（作者裁定）。
