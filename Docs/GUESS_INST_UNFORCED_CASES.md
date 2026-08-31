# `guess_inst` 未被强制的实例化:全链普查的 33 条原文

2026-08-29。数据源:`\<phi>guess_inst_probe` 探测器(`guess_instantiate.ML`,TEMPORARY)在
`Phi_Examples/PhiEx_All.thy` 全链评估(Isa-REPL,6568 s,零错误)中的输出。
总记录 12 728 条、实例化提交 18 053 次,其中**未被强制 33 次(0.183%)**,全部列于此。

**判据回顾**:`?f a₁ … aₙ = r` 判 `forced` 当且仅当 a₁ … aₙ 两两不同且每个都是公式
内部绑定的变量(Miller pattern,此时 `?f := λa₁…aₙ. r` 是唯一解);否则 `UNFORCED`。
`UNFORCED` 只表示"选择不被方程唯一确定",**不**表示这次选择造成了伤害——后者还取决于
该变量是否在别处以不同参数出现,本探测器未记录这一点(见文末)。

`[U]` 后面括号里是参数列表,`:=` 后是被提交的解;`:000`/`:001` 是抽象出来的绑定变量。

## 一、去重后的 17 种形状(共 20 条)

| # | 次数 | 源位置 | 目标 | 提交的实例化 |
|---|---:|---|---|---|
| 1 | 1 | ? | `xa = Inr (?x109 xa)` | `[U] ?x109 (xa) := projr` |
| 2 | 2 | ? | `lookup_tree tr xb = Some (?y41 xb yb)` | `[U] ?y41 (xb, yb) := \<lambda>:000 :001. the (lookup_tree tr :000)` |
| 3 | 2 | ? | `lookup_tree s2 xb = Some (?y41 xb yb)` | `[U] ?y41 (xb, yb) := \<lambda>:000 :001. the (lookup_tree s2 :000)` |
| 4 | 1 | ? | `lookup_tree t2 xb = Some (?y39 xb yb)` | `[U] ?y39 (xb, yb) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 5 | 1 | ? | `lookup_tree t2 xb = Some (?y44 xb yb)` | `[U] ?y44 (xb, yb) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 6 | 1 | ? | `lookup_tree t2 xb = Some (?y49 xb yb)` | `[U] ?y49 (xb, yb) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 7 | 1 | ? | `lookup_tree R' xb = Some (?y39 xb yb)` | `[U] ?y39 (xb, yb) := \<lambda>:000 :001. the (lookup_tree R' :000)` |
| 8 | 1 | ? | `lookup_tree R' xb = Some (?y44 xb yb)` | `[U] ?y44 (xb, yb) := \<lambda>:000 :001. the (lookup_tree R' :000)` |
| 9 | 1 | ? | `lookup_tree R' xb = Some (?y49 xb yb)` | `[U] ?y49 (xb, yb) := \<lambda>:000 :001. the (lookup_tree R' :000)` |
| 10 | 2 | ? | `lookup_tree t2 xa = Some (?y22 xa ya)` | `[U] ?y22 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 11 | 1 | ? | `lookup_tree t2 k1 = Some (?y22 xa)` | `[U] ?y22 (xa) := \<lambda>:000. the (lookup_tree t2 k1)` |
| 12 | 1 | ? | `lookup_tree t2 xa = Some (?y33 xa ya)` | `[U] ?y33 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 13 | 1 | ? | `lookup_tree (insert_tree k1 v1 t2) k1 = Some (?y33 xa)` | `[U] ?y33 (xa) := \<lambda>:000. the (lookup_tree (insert_tree k1 v1 t2) k1)` |
| 14 | 1 | ? | `lookup_tree (insert_tree k1 v1 t2) xa = Some (?y33 xa ya)` | `[U] ?y33 (xa, ya) := \<lambda>:000 :001. the (lookup_tree (insert_tree k1 v1 t2) :000)` |
| 15 | 1 | ? | `lookup_tree t2 xa = Some (?y51 xa ya)` | `[U] ?y51 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 16 | 1 | ? | `lookup_tree t2 xa = Some (?y73 xa ya)` | `[U] ?y73 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 17 | 1 | ? | `lookup_tree (insert_tree k1 v1 t2) xa = Some (?y79 xa ya)` | `[U] ?y79 (xa, ya) := \<lambda>:000 :001. the (lookup_tree (insert_tree k1 v1 t2) :000)` |

## 二、全部 20 条逐条原文

| 序号 | serial | 本记录实例化数 | 其中未强制 | 源位置 | 目标 | 实例化 |
|---:|---|---:|---:|---|---|---|
| 1 | 13947756 | 1 | 1 | ? | `xa = Inr (?x109 xa)` | `[U] ?x109 (xa) := projr` |
| 2 | 16113010 | 1 | 1 | ? | `lookup_tree tr xb = Some (?y41 xb yb)` | `[U] ?y41 (xb, yb) := \<lambda>:000 :001. the (lookup_tree tr :000)` |
| 3 | 16114596 | 1 | 1 | ? | `lookup_tree tr xb = Some (?y41 xb yb)` | `[U] ?y41 (xb, yb) := \<lambda>:000 :001. the (lookup_tree tr :000)` |
| 4 | 16117352 | 1 | 1 | ? | `lookup_tree s2 xb = Some (?y41 xb yb)` | `[U] ?y41 (xb, yb) := \<lambda>:000 :001. the (lookup_tree s2 :000)` |
| 5 | 16120646 | 1 | 1 | ? | `lookup_tree s2 xb = Some (?y41 xb yb)` | `[U] ?y41 (xb, yb) := \<lambda>:000 :001. the (lookup_tree s2 :000)` |
| 6 | 16129488 | 1 | 1 | ? | `lookup_tree t2 xb = Some (?y39 xb yb)` | `[U] ?y39 (xb, yb) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 7 | 16130422 | 1 | 1 | ? | `lookup_tree t2 xb = Some (?y44 xb yb)` | `[U] ?y44 (xb, yb) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 8 | 16131484 | 1 | 1 | ? | `lookup_tree t2 xb = Some (?y49 xb yb)` | `[U] ?y49 (xb, yb) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 9 | 16132378 | 1 | 1 | ? | `lookup_tree R' xb = Some (?y39 xb yb)` | `[U] ?y39 (xb, yb) := \<lambda>:000 :001. the (lookup_tree R' :000)` |
| 10 | 16132798 | 1 | 1 | ? | `lookup_tree R' xb = Some (?y44 xb yb)` | `[U] ?y44 (xb, yb) := \<lambda>:000 :001. the (lookup_tree R' :000)` |
| 11 | 16133380 | 1 | 1 | ? | `lookup_tree R' xb = Some (?y49 xb yb)` | `[U] ?y49 (xb, yb) := \<lambda>:000 :001. the (lookup_tree R' :000)` |
| 12 | 16709026 | 1 | 1 | ? | `lookup_tree t2 xa = Some (?y22 xa ya)` | `[U] ?y22 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 13 | 16709596 | 1 | 1 | ? | `lookup_tree t2 k1 = Some (?y22 xa)` | `[U] ?y22 (xa) := \<lambda>:000. the (lookup_tree t2 k1)` |
| 14 | 16710170 | 1 | 1 | ? | `lookup_tree t2 xa = Some (?y22 xa ya)` | `[U] ?y22 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 15 | 16714784 | 1 | 1 | ? | `lookup_tree t2 xa = Some (?y33 xa ya)` | `[U] ?y33 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 16 | 16715338 | 1 | 1 | ? | `lookup_tree (insert_tree k1 v1 t2) k1 = Some (?y33 xa)` | `[U] ?y33 (xa) := \<lambda>:000. the (lookup_tree (insert_tree k1 v1 t2) k1)` |
| 17 | 16717176 | 1 | 1 | ? | `lookup_tree (insert_tree k1 v1 t2) xa = Some (?y33 xa ya)` | `[U] ?y33 (xa, ya) := \<lambda>:000 :001. the (lookup_tree (insert_tree k1 v1 t2) :000)` |
| 18 | 16720310 | 1 | 1 | ? | `lookup_tree t2 xa = Some (?y51 xa ya)` | `[U] ?y51 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 19 | 16724308 | 1 | 1 | ? | `lookup_tree t2 xa = Some (?y73 xa ya)` | `[U] ?y73 (xa, ya) := \<lambda>:000 :001. the (lookup_tree t2 :000)` |
| 20 | 16725526 | 1 | 1 | ? | `lookup_tree (insert_tree k1 v1 t2) xa = Some (?y79 xa ya)` | `[U] ?y79 (xa, ya) := \<lambda>:000 :001. the (lookup_tree (insert_tree k1 v1 t2) :000)` |

## 三、本文件回答不了的两个问题(需要再跑一次带额外列的探测)

1. **该变量是否在整个目标状态里以不同参数出现在别处**——只有出现了,选错才有代价。
   探测器只记录了 `Logic.nth_prem (n, …)` 这一条子目标,而 `Thm.instantiate` 作用于整个 `st`。
2. **这次实例化是否发生在守卫驳斥器的预处理里**——`preprocess` 先展开 `Premise_def`,
   守卫在被简化时已不带标记;12 728 条里目标含 `Premise`/`MODE_GUARD` 的是 0 条,但这不构成排除。
