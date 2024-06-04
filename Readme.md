Phi-System
--------------

φ-System is an experimental certified programming language and also a generic verification platform.
It aims for reducing the labor effort for obtaining foundationally certified concrete programs (like C).

A neat version for the readme is still in progress and will be updated soon. We refer readers to [Example Gallery](https://xqyww123.github.io/phi-system-html/index.html) for a quick preview of our examples. There are also [some materials](https://drive.google.com/drive/folders/1ABUWcxoQK2h7hF9MXRD1NbJ6jU7wDS-4?usp=sharing) working in progress for interesting readers.

We are always looking for collaborations!

<!-- 
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

The current version works on Isabelle-2022. Please download it from [here](https://isabelle.in.tum.de/).

1. Some additional symbols are required. Please copy lines in file [symbols](https://github.com/xqyww123/phi-system/blob/master/symbols) into your Isabelle symbol file `$HOME/.isabelle/Isabelle2022/etc/symbols`.

2. You maybe need to install a specific font [PhiSymbols](https://github.com/xqyww123/phi-system/tree/master/fonts/PhiSymbols.otf) given in the font directory which defines glyphs of symbols we used in Isabelle.

3. Goto the root directory of φ-System. Execute,
```
isabelle components -u .
```
to add φ-System into components of Isabelle.

4. Now you can build the desired session by command, like,
```
isabelle build Phi_Semantics
```

For semantics of machine integers, we rely on the Word-Lib given by [seL4](https://github.com/seL4/l4v) project and you need to install it from their repo.

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

-->
