## About Exception

I get understood why both of the antecedents in the sequence rule have the same abrupt assertion A.
I thought, I wanted to figure out exact condition for occurence of each exception, but this is useless because, the reason of the exception is to tell something may happen and it may throws on some state, and no matter whether the exception is really throwed the handler will handle the case when the exception occurs, so everything works. Therefore, there is no reason for such accurate condition of the exception. Thus the rule in Simpl is good enough. And from the perspective of forward reasoning, the best we should do is a union of abruption, `{P} C1 {Q} {E1} ==> {Q} C2 {R} {E2} ==> {P} C1 >> C2 {R} {E1 ∪ E2}`.

## About Next Plan

I'm working on the exception. The work is exceptionally smooth and maybe I can finish it today or tomorrow.

About nondeterministic monad, I realize we don't really need that cuz, indeed the send is deterministic when the address is given / decided. And we should indicate the address explicitly as we discussed last Friday, like `{ (addr : A -> B) * ammout * A /\ balance = m /\ addr ⊆ Transitive_Closure } send {B /\ balance = m - ammount}`. This send is deterministic though both A and B are parameters. Then indeed we don't need nondeterministic monad, at least for now.

As for the plan, the demo is the most urgent, so after I finish the exception, maybe we should, in order:
1. do the heaps relating to contracts
2. do the model of virtual methods / classes, including Isar commands
3. do the syntax translator

