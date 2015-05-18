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

#### Semantics of effects (WS)

In the course we have seen how to specify the semantics of mini-programming languages.

Adding *effects*, such as mutable state or concurrency, greatly complicates the definitions of such semantics.

**Project:** define the semantics of a language with effects (in different styles). What can you prove?

Check out: Simon Peyton Jones's paper [Tackling the Awkward Squad](http://research.microsoft.com/en-us/um/people/simonpj/papers/marktoberdorf/mark.pdf) for examples.



#### Semantics of dynamically typed languages (WS)
Falco Peijnenburg, Mark Lekkerkerker

We have mainly considered *statically typed languages* in our lectures.

**Project:** How hard is it to formalise the semantics of dynamically typed languages, such as Python?

Check out: [Gideon Smeding's MSc thesis](http://gideon.smdng.nl/wp-content/uploads/thesis.pdf), describing the semantics of Python



#### Verified compilers (WS) - Rob Spoel, Daniël Heres; Eduard van der Bent & Bert de Vreugd

Given a mini-programming language, interpreter and compiler:


    data Expr = Val Int | Add Expr Expr

    eval : Expr -> Int

    data Instr = PUSH INT | ADD

    compile : Expr -> [Instr]

    exec : [Instr] -> Int


Graham Hutton's book, *Programming in Haskell*, shows how to prove such a compiler is correct, i.e., executing compiled code is the same as evaluation.

**Project:** Extend the source language/compiler/target language with new features.



#### Memory bank in PiWare (WS) - Frank Dedden and Sije Harkema

PiWare is a DSL for hardware description implemented in Agda.

We have implemented several examples of circuits – but most of these are combinational.

**Project:** How can we implement and reason about circuits with feedback loops, such as a memory bank?



#### Reflection and generic programming (WS)

There are many papers explaining how to use *universes* to describe a collection of types in Agda.

These papers typicall avoid the problem of converting a data type to its representation and back.

Recently Agda's reflection mechanism ('Template Agda') has been extended, making it possible to automate this.

**Project:** Write a small library for generic programming in Agda, automating the conversion functions.


#### Functional Pearls in Agda (WS)

There is a large collection of 'functional pearls' – short examples of an elegant function solution to a (seemingly) difficult problem:

  * [Sudoku solver](http://www.cs.tufts.edu/~nr/cs257/archive/richard-bird/sudoku.pdf) - Marcell van Geest & Wilco Kusee
  * [The Gilbreath shuffle](http://yquem.inria.fr/~huet/PUBLIC/shuffle2.pdf)
  * ...

**Project:** Can you implement these pearls in Agda and prove that they are correct?

#### Datatype refinement (JJ)

Olli Linna and Rick Klomp

Given a datatype, construct its refinement rules. For example,


    data Expr = Add Expr Expr
              | Con Int

    refineAdd = ? ~> Add ? ?
    refineCon = ? ~> Con ?


where a question mark denotes a hole.

Given two values of a datatype, construct a sequence of refinements between them (if possible)

Develop heuristics to do this relatively fast 

Fine tune in the context of pretty printing

This work might be useful in the development of a programming tutor such as [Ask-Elle](http://www.staff.science.uu.nl/~jeuri101/homepage/Publications/CEFP/). Technologies from [generic rewriting](http://www.cs.uu.nl/research/techreps/UU-CS-2010-008.html) might be useful.

####￼Datatype coverage (JJ)

Given a datatype and a number of values of the datatype, how much of the
datatype has been covered? This requires a type-indexed datatype (or an
associated type) for storing information in a datatype. The papers on associated
types listed on the materials page are useful here.

Can I relate this to Bayesian networks?

####￼Strategy datatypes (JJ)

Given a strategy for solving a problem, constructing a proof, construct a
datatype for representing instances of the strategy. See [Specifying rewrite
strategies for interactive
exercises](http://www.cs.uu.nl/research/techreps/UU-CS-2009-003.html) to find out what strategies look like.

The result is a generic function with a datatype as result. Again associated
types?

####￼Datatype equality (JJ)
Erik van der Kramer en Morten Asscheman

Generic equality is used a lot.

How do I defined generic equality if I have binding constructs in my datatype?

Can I define generic equality modulo 'theories’ (beta-reduction, eta-reduction, other rewrite rules)?

#### Type-based program construction (JJ)

Djinn implements a decision procedure for intuitionistic propositional calculus

Cannot deal with recursive types.

Extend the procedure using techniques from generic programming to also generate (some) functions for recursive datatypes. 

See the paper [Generating generic functions](http://dl.acm.org/authorize.cfm?key=829746) for a related project in which generic programming and Djinn are used .

