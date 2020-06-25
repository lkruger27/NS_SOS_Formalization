# Formalization of Natural and Structural Operational Semantics
A formalization of Natural and Structural Operational Semantics for the imperative programming language **While** following the theory and notation of Semantics with Applications: A formal introduction by Nielson and Nielson.

[Semantics with Applications: A formal introduction](http://www.cs.ru.nl/~herman/onderwijs/semantics2019/wiley.pdf)

[Made with the help of Software Foundations](https://softwarefoundations.cis.upenn.edu/)

### Table of contents
* [Introduction](#introduction)
* [Purpose](#purpose)
* [Getting started](#getting-started)

### Introduction

This is a Coq formalization of the natural semantics for the imperative programming language **While**. The formalization includes the following topics:
* Framework_common.v: Num, State, Aexp, Bexp, Stm (syntax only).

The Natural Semantics part (in the NS_Formalization directory):
* FrameworkNS.v: framework for Natural Semantics.
* ApplicationNS.v: examples of simple proof trees, semantic equivalence proofs and a determinism proof for Natural Semantics.
* FrameworkAS.v: framework for Hoare logic and annotated programs. It also includes a soundness and completeness proof.
* ApplicationAS.v: examples of Hoare logic and annotated program proofs.
* FrameworkScopes.v: an extension of **While** including Blocks and Procedures. Procedures in dynamic and static scopes.
* ApplicationScopes.v: examples of Blocks and Procedures proofs.
* ExtensionsNS.v: a non-deterministic extension of **While** with an or-rule and an extension of **While** including Break and Continue statements. 

The Structural Operational Semantics part (in the SOS_Formalization directory):
*

### Purpose

This formalization was made as a bachelor thesis by Elly Bahovska and Loes Kruger. Its purpose is to be used in the course Semantics and Correctness to help students understand the proofs better.

### Getting started

The formalization was made in Coq version 8.11.0 with the 64-bit Windows installer.
This version can be downloaded [here](https://github.com/coq/coq/releases/tag/V8.11.0).
There are dependecies between the files so some of the files needed to be compiled correctly before other files can import them. This compiling should be done as follows:
Go to the directory called 'Coq'.
In this directory should be another directory called 'bin'.
Make sure the file that needs to be imported is located in the 'bin' directory.
Open command line and run the following command for the files in the natural semantics part:
```
coqc -Q . NS Name.v
```
Where 'Name' is the name of the file you want to import.
After this, a couple of new files are in the 'bin' directory. The 'Name.vo' needs to be copied to the directory where the Coq files of the formalization are.
If this does not work, try the other options stated in [Software Foundations Chapter Induction](https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html)

