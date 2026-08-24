Phi-System
--------------

φ-System is an experimental certified programming language and also a generic verification platform.
It aims for reducing the labor effort for obtaining foundationally certified concrete programs (like C).

A neat version for the readme is still in progress and will be updated soon. We refer readers to [Example Gallery](https://xqyww123.github.io/phi-system-html/index.html) for a quick preview of our examples. There are also [some materials](https://drive.google.com/drive/folders/1ABUWcxoQK2h7hF9MXRD1NbJ6jU7wDS-4?usp=sharing) working in progress for interesting readers.

We are always looking for collaborations!

### Publication

Qiyuan Xu, David Sanán, Zhé Hóu, Xiaokun Luan, Conrad Watt, and Yang Liu. 2025. Generically Automating
Separation Logic by Functors, Homomorphisms and Modules. Proc. ACM Program. Lang. 9, POPL, Article 67
(January 2025), 40 pages. https://doi.org/10.1145/3704903


### Proof store files

Each theory's proofs are recorded next to it in `<TheoryName>.proof-store`, a binary
append-only log that is committed and distributed with the sources.

Git cannot merge binary files, so this repository ships a driver that concatenates
them — two valid logs concatenated are still a valid log. Enable it once per clone:

    git config merge.proofstore.name   "proof store (concatenate)"
    git config merge.proofstore.driver "tools/proofstore-merge.sh %A %O %B %L %P"

To resolve a `.proof-store` conflict by hand, concatenate both sides:

    git show :2:path/to/Theory.proof-store >  merged.tmp
    git show :3:path/to/Theory.proof-store >> merged.tmp
    mv merged.tmp path/to/Theory.proof-store
    git add path/to/Theory.proof-store


The following instruction is a bit out of date. I will fix it ASAP.

---------------------------------

As a quickview to our language:


writing **foundationally certified**, **high-performant** 

It allows,
1. specifying programs on abstract models, like sets, partial maps, or any algebras defined by users;
2. generating concret imperative programs in C lang (or other langs like Solidity which we plan to support);
3. foundationally certifying the functional correctness of the generated programs.



**foundationally** certified concret imperative programs (like C, Solidity) with high degree of automation for reasoning.

It aims for three goals: 1. foundational verification of minimal trust base, 2. 

reducing the effort of verifying concrete imperative programs (like C & Solidity), and, as a programming language producing certified programs which can be compiled to high-performant targets like C, Solidity or LLVM.

The verification is based on Isabelle and the language is embedded in Isabelle/Isar, enabling users to write and/or verify programs in Isar, enjoying all proof facilities of Isabelle including the famous automated proof search tool Sledgehammer.

The certification of the generated programs is down to the semantics of the target language (e.g. Solidity or LLVM). The semantics of the languages are formalized on an extensible and modular semantics framework.
Formalizations of new languages can reuse the existing common semantic modules and add their own specific features.

The verification and the certified programming is lifted by data refinement onto an abstract domain. Therefore even when the certification is down to concrete semantics of low-level languages, the verification and the programming are always stay in abstraction and able to focus on the algorithm itself.

Expressiveness: higher-order sequential and predicative separation logic combined with hybrid logic for the data refinement, terminable state monad for semantic formalization. Nontermination (coinductive-based like iTree) and coarse-grand concurrency are left for the future. The current aim of the project is to facilate and simplify formal verification in industrial scenario particularly smart contract.

**The development is still in progress and the system is not ready for any use.**
We release the current development as a preview and look for cooperators and contributors.

## Install \& Configuration

The current version works on Isabelle-2023. Please download it from [here](https://isabelle.in.tum.de/).

1. Goto the root directory of φ-System. Execute,
```
isabelle components -u .
```
to add φ-System into components of Isabelle.

    This is the only configuration step. Besides making the sessions of φ-System
    known to Isabelle, the component registers the additional symbols that φ-System
    uses (file [symbols](https://github.com/xqyww123/phi-system/blob/master/symbols))
    and the font providing their glyphs
    ([PhiSymbols](https://github.com/xqyww123/phi-system/blob/master/fonts/PhiSymbols.ttf)),
    by extending the `ISABELLE_SYMBOLS` setting and calling `isabelle_fonts` in
    [etc/settings](https://github.com/xqyww123/phi-system/blob/master/etc/settings).
    There is no need to copy anything into your personal
    `$ISABELLE_HOME_USER/etc/symbols`, nor to install the font into your operating
    system. Restart Isabelle/jEdit afterwards, as the settings are read at startup.

2. Now you can build the desired session by command, like,
```
isabelle build Phi_Semantics
```

For semantics of machine integers, we rely on the Word-Lib given by [seL4](https://github.com/seL4/l4v) project and you need to install it from their repo.

### Optional: a working Nunchaku counterexample finder

Isabelle2025-2's `nunchaku` command ships broken out of the box (the bundled
2017 binary does not know the solver names the frontend sends).  A maintained
build is available as a conda package and is used by φ-System's proof
automation as a fast counterexample guard when present:

```
conda install -c https://conda.qiyuan.me isabelle-nunchaku
```

The package (linux-64; source: [xqyww123/nunchaku](https://github.com/xqyww123/nunchaku))
registers itself as an Isabelle component and sets `NUNCHAKU_VERSION`, which
version-gated consumers use to tell a working install from the bundled one.
Nothing in φ-System's own settings refers to it: without the package,
everything falls back to Nitpick, which is a supported configuration.
Uninstalling the package closes the gate again — no other switch exists or
is needed.

## Examples

Here is a very simple example giving a verified fibonacci function. After the retrun statement and the end of the function body, it generates two proof obligations which are proven by Sledgehammer automatically.

<img src="https://xqyww123.github.io/phi-system/fib.gif" width="500">

The complete verification:

<img src="https://xqyww123.github.io/phi-system/fib.png" width="500">

### More examples

- Several small examples are given [here](https://xqyww123.github.io/phi-system/Unsorted/Phi_Test/PhiTest_Arithmetic.html).
- A medium verification example is the unfinished [Uniswap v3 verification](https://github.com/xqyww123/Uniswap_v).

## Contributions

Contributions are highly welcomed. Please contact us if you are interested in no matter if you are professional in Isabelle or theorem proving.

Any contributor must agree with releasing their contributions in LGPL-v3.0.

## State of the Development

- Kernel Calculus of Programming: done.
- Semantic Framework: may need further improvement.
- Specification Framework:
    - Fictional Separation Logic: under improvement
- Language Features:
    - Variable, local value, breakable branch & loop, return, arithmetics: done.
    - Memories (OO model, C model): WIP.
    - Blockchain-related: WIP

