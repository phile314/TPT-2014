---
title: Projects
layout: default
---

## Projects

In the course on Theory of Programming and Types you have to work on a small project. This page documents some practical matters surrounding these projects.

### Procedure
1. Choose a team. Preferably of 2 people
1. Choose a problem to work on. Some suggestions can be found on the Course material page.
1. Present your research statement to your supervisor
1. Meet with supervisor. Your supervisor should be one of the lecturers
1. Discuss & research this topic
1. Present your results. We will hold a workshop during the exam time for every team to present.
1. Submit a report. See below.

### Criteria
The main focus of the project report and presentation should be the following:

* Research question. Identify a clear and motivated question to answer.
* Research contribution. Develop an implementation or new knowledge to answer the research question.
* Research method. Discuss how you arrived at your answer.
* Related work. Compare your answer with other contributions.

Of course, there is only limited time to work on your research. We expect a brief report, of just a couple of pages (in principle no more than 10 pages), and a short presentation (around 10 - 15 minutes).


## Research Projects

Here are a few ideas for projects. Feel free to get in touch with the supervisor mentioned for more information

### Semantics of effects (WS)

In the course we have seen how to specify the semantics of mini-programming languages.

Adding *effects*, such as mutable state or concurrency, greatly complicates the definitions of such semantics.

**Project:** define the semantics of a language with effects (in different styles). What can you prove?

Check out: Simon Peyton Jones's paper [Tackling the Awkward Squad](http://research.microsoft.com/en-us/um/people/simonpj/papers/marktoberdorf/mark.pdf) for examples.



### Semantics of dynamically typed languages (WS)

We have mainly considered *statically typed languages* in our lectures.

**Project:** How hard is it to formalise the semantics of dynamically typed languages, such as Python?

Check out: [Gideon Smeding's MSc thesis](http://gideon.smdng.nl/wp-content/uploads/thesis.pdf), describing the semantics of Python



### Verified compilers (WS)

Given a mini-programming language, interpreter and compiler:

```haskell
data Expr = Val Int | Add Expr Expr
eval : Expr -> Int
data Instr = PUSH INT | ADD
compile : Expr -> [Instr]
exec : [Instr] -> Int
```

Graham Hutton's book, *Programming in Haskell*, shows how to prove such a compiler is correct, i.e., executing compiled code is the same as evaluation.

**Project:** Extend the source language/compiler/target language with new features.



### Memory bank in PiWare (WS)

PiWare is a DSL for hardware description implemented in Agda.

We have implemented several examples of circuits – but most of these are combinational.

**Project:** How can we implement and reason about circuits with feedback loops, such as a memory bank?



### Reflection and generic programming (WS)

There are many papers explaining how to use *universes* to describe a collection of types in Agda.

These papers typicall avoid the problem of converting a data type to its representation and back.

Recently Agda's reflection mechanism ('Template Agda') has been extended, making it possible to automate this.

**Project:** Write a small library for generic programming in Agda, automating the conversion functions.



### Functional Pearls in Agda (WS)

There is a large collection of 'functional pearls' – short examples of an elegant function solution to a (seemingly) difficult problem:

  * [Sudoku solver](http://www.cs.tufts.edu/~nr/cs257/archive/richard-bird/sudoku.pdf)
  * [The Gilbreath shuffle](http://yquem.inria.fr/~huet/PUBLIC/shuffle2.pdf)
  * ...

**Project:** Can you implement these pearls in Agda and prove that they are correct?

