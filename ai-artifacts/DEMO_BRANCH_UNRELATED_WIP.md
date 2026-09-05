# `origin/demo` 分支上与 C 发射器无关的 WIP 清单

日期：2026-09-05。来源：对 `git diff b2acc405 78b929f3`（分叉点 2024-05-29，demo 末次提交
2024-06-08）逐文件清点，排除代码生成部分。清点由一个 agent 完成，引用的 master 行号均为
该次清点时读取的结果；标 ★ 的条目我另行核实过。

用途：记录 demo 上除发射器之外还做过什么，哪些已经在 master 上，哪些是可以单独搬的独立增量，
哪些绝不能搬。本清单不是待办；这里的任何一项要搬回 master 都需要单独决定。

## 一、与发射器无关、master 上没有的独立工作（可单独考虑）

| # | 项目 | demo 文件 | 内容 | 规模 | master 现状 |
| --- | --- | --- | --- | --- | --- |
| 1 | φ-typeclass 重做 | `Phi_System/library/typeclass.ML`、`Phi_Type.thy`、`IDE_CP_Core.thy`、新 `Phi_Refinement_Algebra.thy`、`Meta_Analysis_PhiTyp.thy` | 新命令 `\<phi>instance`；实例存入 iNet；每个 class 一个 reasoner 组；`complete` 填补例程槽位；默认模式与前提属性登记；元素改为 `(binding, thm)`；`typeclass.ML` 的加载点从 `Phi_Type.thy` 挪到 `IDE_CP_Core.thy`，关键字随之搬。 | 约 440 行 | `typeclass.ML` 与分叉点逐字节相同（173 行，无 `\<phi>instance`），仍在 `Phi_Type.thy:8195` 加载；`Phi_Refinement_Algebra.thy` 不存在。是一块干净的独立增量，只有加载位置一处冲突。 |
| 2 | 过程解析模式 | `library/syntax/procedure.ML`、`library/system/toplevel.ML` | 新 generic data `quantify_mode`/`parameterize_proc` 与 `translate_proc_arg`；允许写 `\<proc> leq ⦃ x ⦂ \<val> T … ⦄` 时不给参数值命名（自动量化或自动应用）。`toplevel.ML` 设为 `(HOL_Quantify, Lambda_Apps)`。示例 `Binary_Search.thy` 的 `generic_binary_search` 依赖它。 | 约 150 行 | 无；`toplevel.ML` 没有 `set_proc_parse_mode`，解析翻译仍直接调 `translate_arg`。 |
| 3 | `application_conv`/`app_conv` 改为 ML 值 | `library/system/application.ML` | 把 `\<phi>Application_Conv` 规则从 theory 引理改成 ML 里的 `@{lemma' …}`，加 `app_conv`；服务于第 1 项的 `build_instance`。 | 约 20 行 | master 仍是 theory 引理（`IDE_CP_Core.thy:1038`）。随第 1 项走。 |
| 4 | `Generic_Variable_Access.arguments_of` | `library/system/generic_variable_access.ML` | 暴露当前参数的 cterm 列表。 | 3 行 | 无。demo 上也没有任何调用者。 |
| 5 | 例程规则去掉 `\<r>Success` 前提 | `PhiSem_CF_Routine_Basic.thy`、`PhiSem_CF_Routine.thy` | `__routine_basic__` 与 `op_routine` 的 `\<r>Success` 前提删除。 | 4 行 | master 保留（`PhiSem_CF_Routine_Basic.thy:20`，`PhiSem_CF_Routine.thy:66,78`）。注意 `reason_using_HHF_assms` 的两次调用形状与此项配套，搬发射器相关项时要一起看。 |
| 6 | `RETURN_FRAME_unit` 用 `\<phi>V_none` | `PhiSem_CF_Routine.thy` | `op_break … (\<phi>arg ())` 改 `… \<phi>V_none`，展开 `\<phi>V_none_def`。 | 2 行 | master 仍是 `(\<phi>arg ())`（`:25`）。 |
| 7 | `op_umul` 改名 `op_mul` ★ | `PhiSem_Machine_Integer.thy` | 纯改名。 | 12 行 | master 仍叫 `op_umul`（`:504`）。发射器钩子 `int.ML` 里的 `op_mul_` 要改回 `op_umul_`。 |
| 8 | `calloc`/`memcpy` 重载集 | `PhiSem_Mem_C.thy`、`PhiSem_Mem_C_AI.thy`、`PhiSem_Mem_C_MI.thy`、`PhiStd_Slice.thy`、`PhiStd_Slice_a.thy`、`Dynamic_Array_arbi_len.thy` | `\<phi>overloads calloc and memcpy`；`calloc`→`calloc_N`、`memcpy`→`memcpy_m`，并给 `calloc_aN`、`calloc_N`、`memcpy_m`、`memcpy_a` 打 `[\<phi>overload …]`；调用点统一写 `calloc (…)`。 | 约 12 行 | master 是裸的 `proc calloc:`（`PhiSem_Mem_C_MI.thy:26`）、`proc calloc_aN:`（`…_AI.thy:18`）、`proc memcpy:`（`PhiStd_Slice.thy:47`）；`Dynamic_Array_arbi_len.thy:100` 仍调 `calloc_aN`。 |
| 9 | `slice_ptr_ToA` 前提拆分 | `PhiSem_Mem_C_Ag_Ar.thy` | 把 `TY' = TY` 从 `\<condition>` 合取里拆成单独的 `\<premise>`。 | 3 行 | master 仍是一个合取（`:191`）。 |
| 10 | `op_load_mem` 体改写 | `PhiSem_Mem_C.thy` | `semantic_local_value(addr)` 的括号应用写法与 `\<semicolon>` 分隔。 | 约 8 行 | master 未改。 |
| 11 | `PhiStd_Loop` 打开类型变量 | `Phi_StdLib/PhiStd_Loop.thy` | `declare [[\<phi>variable_is_typed]]`。 | 1 行 | 无；配置项本身存在（`Phi_Semantics/library/variable.ML:19`）。 |
| 12 | Readme 改写 | `Readme.md` | 以"certified programming language"重新定位，旧文大多注释掉。 | 27 行 | master 仍是分叉点文本。 |
| 13 | 示例改名 | `Binary_Search.thy`、`Rational_Arith.thy` | `generalized_binary_search`→`generic_binary_search`（并改用第 2 项的写法）；`rat_le` 去掉 `[\<phi>overload \<le>]`，改用 `\<phi>instance ‹Order \<rat>›`（依赖第 1 项）。 | 少量 | master 仍是旧名（`Binary_Search.thy:35`，`Rational_Arith.thy:78`）。 |
| 14 | 新的未挂载 theory | `Phi_Examples/Dynamic_Array_demo.thy`（251 行）、`demo/ERC20.thy`（308 行） | 前者是 `DynArr` 的 MI/AI 混合变体，不在 `Phi_Examples/ROOT`；后者导入 `../Phi_Solidity`，该 theory 在任何分支都不存在，且用的是早已废弃的 `argument`/`return` 关键字与 `\<implies>` 写法，从未编译过。 | 559 行 | 均不存在。 |

## 二、master 上已经有的

| 项目 | 说明 |
| --- | --- |
| `Quicksort.thy` 的证明加固 | `linarith_split_limit = 20`、`\<phi>variable_is_typed`、带枢轴位置的不变式、`qsort (i, d-1)`、`t5`/`sorted_simps`。master `Phi_Examples/Quicksort.thy:8,10,46` 与 demo 逐字相同，说明这部分曾手工合并回来。 |
| 死文件的正式版本 | 见第四节：demo 复活的旧拷贝在 master 都有维护中的正式版本。 |

## 三、绝不能搬的

**一次失手的全局替换。** demo 把 `Order` 替换成了空串：常量 `Transformation_Order` 变成
`Transformation_`；章节标题变成 "Canonically ed"、"First  Match"、"Higher  Variables"；
ML 注释里 `OrderMapImpl.sml` 变成 `MapImpl.sml`。波及 `Meta_Analysis_PhiTyp.thy`、
`Phi_Algb_Pre.thy`、`Algebras.thy`、`LCRO_Interval.thy`、`Phi_Preliminary.thy`、PLPR 的
`helpers0.ML` 与 `pattern.ML`，约 20 行。master 是正确的（`Meta_Analysis_PhiTyp.thy:31`
仍是 `Transformation_Order`）。凡是含这种改动的 hunk 一律视为误改。

## 四、死文件与调试残留（不搬）

约 2400 行的 diff 是没有任何 theory 加载的文件：

- `Phi_System/library/tools/{Hook, where_tac, inhabited_rule, optional_translation, helps}.ML`、
  `library/syntax/param.ML`、`library/additions/delay_by_parenthenmsis.ML`：其中 `Hook.ML`、
  `where_tac.ML`、`param.ML` 是 PLPR 正式文件（`Phi_Logic_Programming_Reasoner/library/…`）的
  旧拷贝；`helps.ML` 为 0 字节。
- `Phi_Semantics_Framework/fiction_space{,_more}.ML`：`Phi_System/library/spec_framework/` 下
  正式文件的旧拷贝。
- `Phi_Logic_Programming_Reasoner/Phi_Logic_Programming_Reasoner.thy`：`PLPR.thy` 的 1360 行
  旧拷贝，不在 ROOT。
- `Phi_System/library/system/procedure2.ML`、`PLPR/library/reasoner2.ML`：只有 `open X` 的空壳；
  `PLPR/library/default_pattern.ML` 为 0 字节。

调试残留（约 40 行）：`PhiSem_Int_ArbiPrec.thy` 的 `[[\<phi>trace_reasoning = 2]]`，
`PhiSem_Mem_C.thy`、`PhiSem_Mem_C_Ar_MI.thy`、`PhiSem_CF_Basic.thy` 里的 `term`/`thm`，
`PhiTest_Arithmetic.thy` 的 `[[\<phi>hide_techinicals=false]]`，`Quicksort.thy` 里注释掉的
`qsort_rat`/`qsort_generic`，`PhiSem_Play_Ground.thy` 删掉的一个测试过程，以及十来处空白改动。

## 五、交叉引用：发射器需要的、不在本清单里的项

以下几项 demo 上有、master 上无，且发射器依赖，归入移植计划而不在本清单：

- 过程参数按 `input` 顺序排列（`closure precond`、`package_values` 的 `sort` 参数）；
- `Phi_Reasoner.reason_using_HHF_assms`（PLPR `reasoner.ML`，`cf_routine.ML` 两处调用）；
- `basic_recursion.ML` 的逐条前提聚合与递归变量推断修正；
- unit 元数的 `Semantic_Types_i` 规则放宽为任意 `X`（`IDE_CP_Reasoning1.thy`，★ 已搬）；
- `Phi_Syntax.dest_procT_params`；
- 示例与测试的 `is [routine]`、显式 `return`、带类型变量。
