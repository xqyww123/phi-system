- Anti-quotation of applicative rules in synthesis
- Eliminational φ-LPR, necessary in Inhabitance rule generation? Yes, the system RS uses an inefficient loop. We need item net.
- Explicit flag to control backtrack in PLPR
- if ‹$initialized› -> if $initialized
- Simplify inhabitance reasoning using [useful,simp]. The auto lemma φ is too redundent making auto reasoning taks a lot time (partially done. i'm not sure if there are others)
- Remove Inhabited that fails to reason, in Inhabited reasoning (I don't know if we really want this)
- type check / give type in $value
- Auto detect form (?R * X) at the begining of casting or ToSA, and convert it to (X remains ?R)

- Auto mechanism for generating implication rules using constructφ
- Hide scaffolding/helper rules, to optimize sledgeharmer. [long term work]

