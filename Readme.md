The current version works on Isabelle-2021-1.

Some additional symbols are required. Please **copy lines** in file `symbols` into your Isabelle symbol file `$HOME/.isabelle/Isabelle2021-1/etc/symbols`.
You may also need to install the *Symbola* font given in directory `fonts`.

------------------

The cleaning is working in progress, so the root directory now is a big mess!

The list of documented modules (sessions), in the order of dependency:
- Phi_Logic_Programming_Reasoner
- Phi_Algebras
- Virtual_Datatype (in directory Phi_Semantics_Framework/Virt_Datatype, may also see Virtual_Datatype_Doc)
- Phi_Semantics_Framework

Working in Progress:
- Phi_System (it is a very big module and the main content of our work.)

The session names are identical to their directory names, unless stated specially.

Use `isabelle document -O <desired-output-directory> <session-name>` to generate the documents! You may need to configure your latex environment but most of the dependencies are given in texlive.


