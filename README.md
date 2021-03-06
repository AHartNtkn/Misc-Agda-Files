Misc-Agda-Files
===============

These are an assortment of functions and programs made by Anthony Hart in the programming language Agda
(http://wiki.portal.chalmers.se/agda/pmwiki.php).

Currently, the directory has the following files;

sorting.agda
- Includes a general definition of Sorted Lists over Total Orders, and an implementation of insertion sort.
- Includes three different implementations of Merge Sort, one of them passing the termination checker.
- Includes an implementation of the discrete log base 2.
- Includes a proof that the natural numbers form a total order with ≤, for testing the sorting functions.

BLC.agda
- Includes a very nice implementation of the (untyped) Lambda Calculus
- Includes an implementation of the SK Calculus (untested, probably wrong)
- Includes functions for translating back and forth between SK and Lambda calculi (untested)
- Includes an implementation of the Jot language (http://semarch.linguistics.fas.nyu.edu/barker/Iota/#Goedel) (untested)
- Includes a definition and a (messy) implementation of deBrujin Lambda Calculus
- Includes functions for translating back and forth between deBrujin terms and lambda terms
- Includes an implementation of the Binary Lambda Calculus, the reason the file is called BLC
  (http://homepages.cwi.nl/~tromp/cl/LC.pdf)

FixedPoint.agda
- File created to formalize some of the results in http://arxiv.org/pdf/math/0305282v1.pdf
- Contains a proof of Lawvere's fixed point theorem over types and functions (I hope to extend it to the full theorem at some point.)
- Contains a proof of Cantor's Theorem as an instance.
- Contains disproof of Church's thesis

MuRecursion.agda
- Contains an implementation of the μ-recursive functions
