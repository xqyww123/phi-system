Proposal - an axiomatic approach fixing our semantic locale with minimal cost of trust
====

Instead of using locale everywhere, we fix a locale by axiomization once it is declared.
Specifically, we declare type constants and term constants for each type and term variable in the locale, axiomize the assumptions of the locale, and instantiate the locale by these constants and axioms.

A problem is, of course it introduces unverified axioms, so how do we verify the axioms are consistent?
A solution is from meta level:
Because the terms and types are only declared but not specified, they can be regarded as free variables from a meta perspective.
Once the locale is finally instantiated by some constants that do not depend on the axiomatically declared types and terms, then from meta level we can instantiate the axiomatically declared types and terms to be those constants, and then the axioms are verified by the instantiation logically.
We can asks users to finally instantiate the locale as a kind of delayed proof obligation.
And it can be done by a ML program as an extension of the trust kernel.

Problem: How do we check that the user-provided instantiations do not depend on the axiomatically declared terms and types, when the terms and types are declared earlier than the user instantiation?
Solution: in a word, rely on the *theory dependency* which is also in the kernel of Isabelle.
Specifically, we ask the locale is given in theory A, the axiomization is given in theory B which depends on A, and the final instantiation is given in another theory C depending on A but NOT on B.
If it is held, it is then a valid certification for that the instantiation in C does not depend on the axiomatically declared terms and types in B, so the instantiation in C vindicates the consistency of the axioms in B.
So, our ML kernel just checks this theory dependency.

The increment of the trust base is just this ML kernel, of 20 ML lines about.


