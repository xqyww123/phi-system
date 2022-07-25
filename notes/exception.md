### Exception

{P} C {Q} {E} := (∀x ∈ P. case C x of Success y => y ∈ Q | Exception y => y ∈ E | PartialCorrect => true | Invalid => false)

PartialCorrect means nontermination.
Invalid means malformed program.

#### Throw

The operation `throw e` first pushes e onto the expression stack, and then returns an exception state.
`throw e := (push e >> (λs. Exception s))`

The exception object is put on the first element of the expression stack.

#### Catch

The handler is a procedure. This procedure receives the exception object as the first element of the expression stack.
It should first case-switch the type of the exception object, and call correponding handler for each type.



