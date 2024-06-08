We should divide PartialCorrect into two things, NonTerminable and AssumptionBorken.

NonTerminable is to be ready for total correctness one day.

The framework still needs AssumptionBroken. size_t is a good case for this.
The framework is general so the size_t of the machine is an unspeficied parameter.
Then in the program, to evaluate `size_of T` we must assume the size_t is at least as large as the size of the type T. This proof obligation of this assumption is discharged during compilation when the size_t is decided.

```
size_t T = assume (size_of T ≤ 2^size_t) >> ...
```
