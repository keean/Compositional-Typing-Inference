Compositional-Typing-Inference
==============================

Compositional inference of principal typings for simple lamda-calculus based language written in C++

remember to checkout the submodule with the following commands from the root of the project after cloning:

*git submodule init*  
*git submodule update*

It currently types lambda calculus + let, here is an example to show the syntax, and a typical typing derivation:

*Input*
\y . (let f = x y in let x = z y in q w)

*Output*
1.  [var x]            x : {x : a} |- a
2.  [var y]            y : {y : a} |- a
3.  [app (1) (2)]      (x y) : {x : (a -> b), y : a} |- b
4.  [var z]            z : {z : a} |- a
5.  [var y]            y : {y : a} |- a
6.  [app (4) (5)]      (z y) : {y : a, z : (a -> b)} |- b
7.  [var q]            q : {q : a} |- a
8.  [var w]            w : {w : a} |- a
9.  [app (7) (8)]      (q w) : {q : (a -> b), w : a} |- b
10. [let x (6) (9)]    (let x = (z y) in (q w)) : {q : (a -> b), w : a} |- b
11. [let f (3) (10)]   (let f = (x y) in (let x = (z y) in (q w))) : {q : (a -> b), w : a} |- b

