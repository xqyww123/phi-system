# C 发射器移植计划（从 `origin/demo` 分支移回 master）

日期：2026-09-05。状态：草案，待批准。

## 0. 原则

1. demo 分支（`78b929f3`，2024-06-08）的设计**原样移植**：`[\<phi>export]` 属性、
   `\<phi>export_code` 配置、`Theory.at_end` 钩子、`Generated` 记录、每个 theory 一个
   ML 结构、`open_self` 合并手写钩子与生成的 `val`、文件写在 theory 文件旁边。
2. 只允许两类改动：
   - **对接改名**：demo 之后 master 上改了名字的常量、类型、theory、ML 结构，把钩子文件里
     的名字对上。这一类在 §3 逐条列出，每条附证据。
   - **需要批准的改变**：任何不属于纯改名的改动，在 §4 逐条列出，默认"不改"，等你决定。
3. 不搬 demo 分支上与代码生成无关的 WIP（typeclass、where_tac、Hook.ML、inhabited_rule、
   optional_translation、CoP-paper、demo/ERC20.thy、notes/、`codegen_LLM/`、旧 `codegen/`）。
4. 不运行 `isabelle build`。需要构建时列出命令请你执行。

## 1. demo 设计回顾（作为核对基准）

一句话：把过程的定义定理 `c ≡ 程序体` 逐字转写成一段 ML 源码并求值；求值得到的 ML 值是
打印单子里的函数，跑起来写出 C 文本。

- `Phi_System/library/codegen/emit.ML`：转写器 `Phi_CG_Emit`。常量 `Thy.c` 转成
  `C'G_Thy.c_`，同 theory 的常量转成 `c_`，类型构造子 `Thy.t` 转成 `C'G_Thy.t_T`，
  `Abs` 转成 `fn`，`LABEL_TAG` 转成字符串，`TYPE(τ)` 转成类型映射。`gen_extractor`
  为一个 theory 生成 `structure C'G_<Thy> = struct [open C'G_<Thy>] val … end`，
  接口表非空时追加 `val _ = Phi_C'G.codegen "<path>.C" (I #> Phi_CG.interf "名" (项) …)`。
- `Phi_System/library/codegen/base.ML`：打印单子 `Phi_CG`。状态 = (缓冲区栈, 待用函数名,
  已生成函数表, 已完成代码块, 变量计数)。`fun_name` 为每个过程常量持有一个名字格子，
  `new_fun` 保证每个函数只定义一次，`interf` 把导出名塞进待用函数名，`codegen'` 写文件。
- `Phi_System/library/codegen/C/base.ML`：C 专用的打印原语 `Phi_C'G`（`var`、`unop`、
  `binop`、`defty` 等），前导为三行 `#include`。
- `Phi_System/library/codegen_nonkernel/emit.ML`：配置 `\<phi>export_code`、`Generated`
  记录、`codegen'`、`Theory.at_end` 钩子。
- `Phi_System/library/system/procedure.ML`：`Procedures` 登记表（每 theory 的定义定理
  列表，经 `Local_Theory.declaration` 登记）、`Interfaces` 表（导出名 → 项）、
  `[\<phi>export 名 for 项…]` 属性。
- `Phi_Semantics/codegen/…`：各语义模块的手写钩子，每个文件一个 `C'G_<Thy>` 结构。
- 使用方式：`proc f [\<phi>export]:` 或 `declare f_def [\<phi>export g for TYPE(…)]`，
  theory 末尾 `declare [[\<phi>export_code = C]]`。

## 2. 移植清单

### 2.1 从 demo 逐字复制的文件（`git show 78b929f3:<路径>`）

| 目标路径（相对 `contrib/phi-system`） | 行数 | 备注 |
| --- | --- | --- |
| `Phi_System/library/codegen/emit.ML` | 59 | 原样 |
| `Phi_System/library/codegen/base.ML` | 45 | 原样 |
| `Phi_System/library/codegen_nonkernel/emit.ML` | 33 | 原样 |
| `Phi_System/library/codegen_nonkernel/base.sig` | 28 | 原样 |
| `Phi_System/library/codegen_nonkernel/C/base.sig` | 20 | 原样 |
| `Phi_System/library/codegen/C/base.ML` | 28 | 原样 |
| `Phi_System/library/codegen/C/misc.ML` | 29 | 原样 |
| `Phi_System/library/codegen/C/Phi_Semantics_Framework.ML` | 12 | 原样 |
| `Phi_System/library/codegen/C/Element_Path.ML` | 4 | 原样 |
| `Phi_System/library/codegen/C/symbol.ML` | 1 | 需对接改名，见 §3.4 |
| `Phi_System/library/codegen/C/List.ML` | 0 | 空文件，原样保留 |
| `Phi_System/library/codegen/C/formalization_tool.ML` | 0 | 空文件，demo 未加载，不搬 |
| `Phi_Semantics/codegen/bool.ML` | 8 | 需对接改名，见 §3.1 |
| `Phi_Semantics/codegen/C/int.ML` | 22 | 需对接改名，见 §3.1 |
| `Phi_Semantics/codegen/C/aint.ML` | 9 | 需对接改名，见 §3.1 |
| `Phi_Semantics/codegen/C/pointer.ML` | 4 | 需对接改名，见 §3.1 |
| `Phi_Semantics/codegen/C/pointer_arith_MI.ML` | 5 | 原样 |
| `Phi_Semantics/codegen/C/CF.ML` | 18 | 原样 |
| `Phi_Semantics/codegen/C/routine.ML` | 15 | 原样 |
| `Phi_Semantics/codegen/C/break.ML` | 8 | 原样 |
| `Phi_Semantics/codegen/C/var.ML` | 7 | 原样 |
| `Phi_Semantics/codegen/C/mem.ML` | 7 | 原样 |
| `Phi_Semantics/codegen/C/agg_base.ML` | 7 | 结构名需改，见 §3.2 |
| `Phi_Semantics/codegen/C/agg_ntup.ML` | 6 | 需对接改名，见 §3.1、§3.4 |
| `Phi_Semantics/codegen_nonkernel/C/agg_ntup.sig` | ? | 原样（签名文件） |
| `Phi_Semantics/codegen_nonkernel/C/break.sig` | ? | 原样 |
| `Phi_Semantics/codegen/C/void.ML` | 0 | 空文件，原样保留 |
| `Phi_Semantics/codegen/agg_array.ML` | 0 | 空文件，原样保留 |
| `Phi_Semantics/codegen/C.ML` | 0 | 空文件，原样保留 |
| `Phi_Semantics/PhiCG_C.thy` | 6 | 原样（`imports Phi_System.IDE_CP`，`ML_file codegen/C.ML`） |

`Phi_Semantics/codegen/aggregate_base.ML`、`routine_C.ML` 在 demo 末次提交时为空且
无人加载，不搬。

### 2.2 对既有文件的改动（按 demo 的 diff `git diff b2acc405 78b929f3`）

1. `Phi_System/library/system/procedure.ML`
   - 签名：删 `type interface`，加 `type export_name = string`；
     `interfaces_of : theory -> term Symtab.table`；
     `procedures_of : Context.generic -> thm list`；
     `add_interface : export_name * term -> theory -> theory`；
     `add_procedure : thm -> Context.generic -> Context.generic`。
     删 `compilation_thm_of`（master 上无调用者；demo 也删了）。
   - 把注释中的 `Procedures` 登记表恢复为 demo 版本（元素为定义定理，
     `thy_name_of_ctxt = Context.theory_long_name o Context.theory_of`）。
   - `gen_define` 里 `Local_Theory.define` 之后加
     `Local_Theory.declaration {syntax=false, pervasive=false, pos=Binding.pos_of binding}
        (fn m => add_procedure (Morphism.thm m def))`。
   - 文件末尾加 `Interfaces`（`term Symtab.table Symtab.table`）、`interfaces_of`、
     `add_interface`、`chk_interf_thm` 和 `[\<phi>export]` 属性，逐字取 demo。
   - master 现有的 `Interfaces`/`interfaces_of`/`add_interface`（元素为 `{name, thm}`）
     和注释块里的 `add_interface_command` 删除，与 demo 一致。
   - `closure` 的参数排序：见 §4.1。
2. `Phi_System/library/syntax/Phi_Syntax.ML`：加 `dest_procT_params`（demo 原文，
   紧跟 `is_procT` 之后，签名同步加 `val dest_procT_params : typ -> typ list`）。
3. `Phi_System/library/syntax/procedure.ML`：见 §4.1。
4. `Phi_System/IDE_CP_Core.thy`：在 `subsubsection ‹Setups›` 之前插入 demo 的
   `subsubsection ‹Codegen›` 及其十行 `ML_file`（顺序照 demo）。不搬 demo 同一 diff 里的
   `\<phi>typeclass`/`\<phi>instance` 关键字和 `library/typeclass.ML`。
   `procedure.ML` 的加载位置见 §4.2。
5. `Phi_Semantics/*.thy` 末尾各加一行 `ML_file`（照 demo diff）：
   `PhiSem_Aggregate_Array`(agg_array.ML)、`PhSm_Ag_Base`(C/agg_base.ML，demo 里是
   `PhiSem_Aggregate_Base`)、`PhiSem_Aggregate_Named_Tuple`(codegen_nonkernel/C/agg_ntup.sig
   + C/agg_ntup.ML)、`PhiSem_CF_Basic`(C/CF.ML + 那行 `setup`)、`PhiSem_CF_Breakable`
   (codegen_nonkernel/C/break.sig + C/break.ML)、`PhiSem_CF_Routine`(C/routine.ML)、
   `PhiSem_Generic_Boolean`(bool.ML)、`PhiSem_Int_ArbiPrec`(C/aint.ML)、
   `PhiSem_Machine_Integer`(C/int.ML)、`PhiSem_Mem_C`(C/mem.ML)、
   `PhiSem_Mem_C_Ar_MI`(C/pointer_arith_MI.ML)、`PhiSem_Mem_Pointer`(C/pointer.ML)、
   `PhiSem_Variable`(C/var.ML)、`PhiSem_Void`(C/void.ML)。
   `PhiSem_CF_Basic` 的那行 `setup ‹… codegen' {lang="C"} true Symtab.empty @{thms' if_def} …›`
   原样搬：master 上 `proc "if"` 仍在（`PhiSem_CF_Basic.thy:118`），`if_def` 存在。
6. 测试与示例（§5）。

## 3. 对接改名（证据均来自 master 源码）

转写按名字进行，所以凡是 demo 之后改了名的常量或类型，钩子文件里对应的 ML 标识符要跟着改。
改名规则：`tr_name` 把 `\<`、`<` 删掉、`>` 换成 `_`；常量加后缀 `_`，类型加后缀 `_T`。

### 3.1 语义类型常量与类型

| demo 钩子里的标识符 | demo 时的 Isabelle 名 | master 上的名 | 新标识符 | 证据 |
| --- | --- | --- | --- | --- |
| `i_n_t__T`（int.ML） | 类型 `\<i>\<n>\<t>` | 类型 `int_t`（记法 `\<int'>`） | `int_t_T` | `PhiSem_Machine_Integer.thy:64` |
| `b_o_o_l__`（bool.ML） | 常量 `\<b>\<o>\<o>\<l>` | `sem_bool_T`（记法 `\<bool'>`） | `sem_bool_T_` | `PhiSem_Generic_Boolean.thy:10` |
| `p_o_i_n_t_e_r__`（pointer.ML） | 常量 `\<p>\<o>\<i>\<n>\<t>\<e>\<r>` | `sem_pointer_T`（记法 `\<ptr>`） | `sem_pointer_T_` | `PhiSem_Mem_Pointer.thy:17` |
| `a_i_n_t__`（aint.ML） | 常量 `\<a>\<i>\<n>\<t>` | `sem_aint_T`（记法 `\<aint>`） | `sem_aint_T_` | `PhiSem_Int_ArbiPrec.thy:13` |
| `semty_ntup_`（agg_ntup.ML） | 常量 `semty_ntup` | `sem_ntup_T` | `sem_ntup_T_` | `PhiSem_Aggregate_Named_Tuple.thy:8` |

其余指令常量名（`op_add`…`op_cast_int`、`op_if`/`op_sel`/`op_do_while`、`op_routine`/
`op_rec_routine`、`op_break`、`op_var_scope`/`op_get_var`/`op_set_var`、`op_load_mem`/
`op_store_mem`/`calloc1`/`mfree`、`op_get_element_pointer`、`op_add_ptr`/`op_add_ptr_unsigned`、
`op_get_aggregate`/`op_set_aggregate`/`op_construct_aggregate`、`semantic_named_tuple_constructor`、
`sem_mk_int`/`sem_mk_aint`/`mk_int_T`、`op_const_int`/`op_const_bool`、`\<phi>V_*`、`Return`/
`bind`/`unreachable`/`\<phi>arg`、`LABEL_TAG`）在 master 上同名同 theory，已逐一 grep 核对。
**参数顺序或类型参数是否变过无法靠读源码保证**，只能在 §5 跑例子时暴露。

### 3.2 theory 改名

`PhiSem_Aggregate_Base` → `PhSm_Ag_Base`：`agg_base.ML` 里的结构名
`C'G_PhiSem_Aggregate_Base` 改为 `C'G_PhSm_Ag_Base`，`ML_file` 行放在 `PhSm_Ag_Base.thy` 末尾。

### 3.3 `aggregate_index'`

demo 的 `Element_Path.ML` 假设 `AgIdx_N/S/V` 属于 theory `Phi_Element_Path`；master 上仍是
`Phi_System/Phi_Element_Path.thy:20`，不用改。

### 3.4 符号（命名元组字段名）

demo 的 `symbol.ML` 把常量 `PhiTool_Symbol.symbol.mk_symbol` 映射到
`Phi_Tool_Symbol.revert_symbol1`，当时符号的参数是一个数字。master 上符号类型搬到了
`Performant_Isabelle_HOL.SSymb`（`Phi_Element_Path.thy:2` 导入），构造子是 typedef 态射
`SSymb.mk_symbol`，参数不再是数字，而是由常量 `SSymb.Z` 与 `SSymb.A`…`SSymb.F` 组成的
双射六进制链（`contrib/Performant_Isabelle_ML/library/ssymb.ML:25-40`）。
`Phi_Tool_Symbol.revert_symbol1 : int -> string` 仍在（`ssymb.ML:60`）。

因此 `symbol.ML` 改为一个 `C'G_SSymb` 结构：`Z_ = 0`，`A_ … F_` 各为
`fn r => 6*r + k`（k = 1…6），`mk_symbol_ = Phi_Tool_Symbol.revert_symbol1`。这样
`mk_symbol (B (A Z))` 转写求值后得到原来的标识符字符串，与 demo 行为一致。
这个文件按"对接改名"处理，但因为内容重写，也列在 §4.4 请你过目。

## 4. 需要你批准的改变（默认不改）

### 4.1 过程参数的排序（demo 对 `closure` 的改动）

demo 把 `closure ctxt substT f` 改成 `closure precond substT f`：先从前置条件（`input`
规格）收集值变量，按它们在 `input` 里出现的顺序给程序体里的值排序，再打包成参数元组。
目的是让 C 函数的参数顺序与 `input` 的书写顺序一致（demo 里未排序前生成过
`GCD(int v1, int v0)`）。为此 demo 给 `Procedure_Syntax.package_values` 和
`package_values0` 加了一个 `sort` 参数，并导出 `collect_vals`。

移植方式的提议：**不改 `package_values` 的签名**。master 的 `package_values name R2L Vs0 term`
已经接受显式的值列表 `Vs0 = SOME …`，所以在 `closure` 里用 master 的 `collect_vals`
分别收集 `precond` 和 `f` 的值，按 demo 的 `sort'` 规则排序后作为 `Vs0` 传入即可。
需要把 `collect_vals` 从 `local` 块里导出到 `PROCEDURE_SYNTAX` 签名。行为与 demo 完全相同，
改动面比 demo 小。

需要你知道的后果：这会改变 master 上**所有** `proc` 定义出的常量的参数顺序（当程序体里值的
出现顺序与 `input` 顺序不同时）。任何直接依赖 `_def` 参数顺序的地方都会受影响；
`_\<phi>app` 规格定理不受影响。

选项：(a) 按上述方式移植；(b) 按 demo 原样改 `package_values` 签名（要改
`procedure3.ML`、`Phi_Working_Mode.ML`、`gen_synthesis_rule.ML` 三处调用）；(c) 不搬这项，
接受参数顺序按程序体出现顺序。

### 4.2 `procedure.ML` 的加载位置

demo 把 `ML_file "library/system/procedure.ML"` 从 `sys0.ML` 之前移到
`generic_variable_access.ML` 之后。diff 里看不出原因。提议：先保持 master 顺序，
若编译报未绑定标识符再按 demo 移动，并在此文档记录原因。

### 4.3 示例与测试文件的改动

demo 为了跑通发射，改了示例本身：

- `Phi_Test/PhiTest_Arithmetic.thy`：加 `declare [[\<phi>variable_is_typed]]`（`var.ML` 的
  `chkT` 在未开启时报错）；`test_prime`/`test_prime'`/`GCD` 加 `[\<phi>export …]`；
  `GCD` 和 `test_prime'` 的分支体改写为显式 `return (…)`；末尾
  `declare [[\<phi>export_code = C]]`；导入 `Phi_Semantics.PhiCG_C`。
- `Phi_Examples/Linked_List.thy`：给七个过程加 `is [routine]`（master 上只有三个带）；
  `[\<phi>export for \<i>\<n>\<t>]` 需改为 master 的类型项（待定，`\<int'>` 对应
  `mk_int_T TYPE(int_t)`）；末尾开配置。
- `Phi_Examples/Quicksort.thy`、`Dynamic_Array.thy`：加 `[\<phi>export]` 与配置。
- `Phi_Examples/Rational_Arith.thy`：demo 导出的 `rat_add` 等在 master 上已不存在，跳过。

提议：第一阶段只改 `PhiTest_Arithmetic.thy`，且只加三样：`variable_is_typed`、三个
`[\<phi>export]`、末尾配置和导入；**不改写** GCD 与 test_prime' 的分支体。若发射对
"分支落值"风格失败，报告给你再定。示例文件第二阶段再动。

### 4.4 `symbol.ML` 的重写

内容见 §3.4。虽属对接，但是整文件重写，请过目。

### 4.5 `PhiCG_C.thy` 与 ROOT

demo 没有把 `PhiCG_C` 加进 `Phi_Semantics/ROOT`，由导入它的 theory 按需加载。提议保持不变。

## 5. 顺序与验证

1. 复制 §2.1 文件，做 §3 改名，改 §2.2 各处。
2. 请你运行：`isabelle build -d contrib/phi-system Phi_Semantics`，看 ML 编译是否通过
   （钩子文件的 ML 错误在这一步暴露）。
3. 改 `PhiTest_Arithmetic.thy`（§4.3 第一阶段），请你运行
   `isabelle build -d contrib/phi-system Phi_Test`。theory 结束时应在
   `Phi_Test/PhiTest_Arithmetic.C` 生成 `test_prime`、`test_prime2`、`GCD` 三个 C 函数。
   转写求值失败会以 ML 错误出现在 `end` 命令处，并带生成的 ML 源码（`gen_extractor`
   有 `tracing src`）。
4. `gcc -fsyntax-only Phi_Test/PhiTest_Arithmetic.C`；再写一个小 `main` 调 `GCD`
   与 `test_prime` 对若干输入比对（本机有 `/usr/bin/gcc`，无 clang）。demo 生成的
   `Phi_Test/PhiTest_Arithmetic.C` 可作为输出形状的对照。
5. 第二阶段：`Quicksort`、`Linked_List`、`Dynamic_Array`，各与 `Phi_Examples/*.c` 手写
   参考实现做差分测试。这一阶段涉及 §4.3 的示例改动，届时再逐项请示。

## 6. 已知但本计划不处理的事

- 指针在 demo 里一律 `void*` 加强制转换；结构体靠 `typedef` 匿名 struct。原样保留。
- `Phi_Test/PhiTest_Arithmetic`（无扩展名的文件）是 demo 早期的错误输出（`GCD(v1v0)`），不搬。
- 与并行改造（choice 定义的常量）的衔接：发射器读 `_def`，只要将来程序体所在的常量也有
  `_def` 并登记进 `Procedures`，发射器不需要改。
