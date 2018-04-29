Toward $\pi$-calculus in idris
==============================

_WIP by [Dan Connolly][dckc], Apr 2018_

_This is a [literate idris][lp] document, with idris code ..._

> module picalc2
> 
> %access export
> %default total


_... interspersed with text from ..._

* Milner, Robin. _[The polyadic π-calculus: a tutorial.][RM93]_
  In Logic and algebra of specification, pp. 203-246.
  Springer, Berlin, Heidelberg, 1993.

_We're having some fun with [KaTeX][] while we're at it._

[dckc]: http://www.madmode.com/contact/
[RM93]: https://pdfs.semanticscholar.org/5d25/0a3a14f68abb1ae0111d35b8220b4472b277.pdf
[lp]: http://docs.idris-lang.org/en/latest/tutorial/miscellany.html#literate-programming
[KaTeX]: https://khan.github.io/KaTeX/


2.1 Basic ideas
---------------

The most primitive entity in $\pi$-calculus is a _name_. Names,
infinitely many, are $x, y, ... \in \mathcal{X}$; they have no
structure. In the basic version of $\pi$-calculus which we begin
with, there is only one other kind of entity; a _process_.
Processes are $P, Q, ... \in \mathcal{P}$ and are built from names
by this syntax

  $$P ::= \Sigma_{i\in I}\pi_i.P_i \;|\; P|Q \;|\; !P \;|\; (\nu x)P$$

> {- `mutual` lets us forward reference Action from Process.-}
> 
> syntax [p] "|" [q] = Par p q;
> syntax "!" [p] = (Replicated p);
>
> mutual
>   ||| Processes are built from names, so `Process` is a
>   ||| type constructor from names.
>   data Process : {name: Type} -> Type where

The summation form represents a process able to take part in one --
but only one -- of several alternatives for communication.

>     Sum: (List (Action {name}, Process {name})) -> Process {name}

$P | Q$ -- "$P$ par $Q$" -- simply means that $P$ and $Q$ are
concurrently active.

>     Par: (P: Process {name}) -> (Q: Process {name}) -> Process {name}

$!P$ -- "bang $P$" means $P|P|...$ as many copies as you wish.

>     Replicated: (P: Process {name}) -> Process {name}

$(\nu x)P$ -- "new $x$ in $P$" -- restricts the use of the name $x$ to $P$. 

>     New: (x: name) -> (P: Process {name}) -> Process {name}

In a summand $\pi.P$ the prefix $\pi$ represents an _atomic action_,
the first action performed by $\pi.P$.

>   data Action : {name: Type} -> Type where

There are two basic forms of prefix:

 - $x(y)$, which binds $y$ in the prefix process, means
   "input some name -- call it $y$ -- along the link named $x$"

>     Input: (x: name) -> (y: name) -> Action {name}

 - $\bar{x}y$ , which does not bind $y$, means "output the name $y$
   along the link named $x$".

>     Output: (x: name) -> (y: name) -> Action {name}
>

In the case $I = \emptyset$, we write the sum as $0$.

> zero: Process
> zero = Sum []

We call $x$ the _subject_ ...

> subject: Action {name} -> name
> subject (Input x y) = x
> subject (Output x y) = x

We call ... $y$ the _object_

> object: Action {name} -> name
> object (Input x y) = y
> object (Output x y) = y

2.2 Some simple examples
------------------------

_typo?_

Note that $R$ has become $\bar{y}v$ or $\bar{z}v$; ...

_should be:_

Note that $Q$ has become $\bar{y}v$ or $\bar{z}v$; ...

_no?_

2.3 Structural Congruence
-------------------------

_Note: In order to convince idris of the [totality][] of `fn` and
`bn`, we use `assert_smaller` to help it understand that `(Sum rest)`
is structurally smaller than `(Sum ((pi, P) :: rest))`._

[totality]: http://docs.idris-lang.org/en/latest/reference/misc.html?highlight=assert_smaller#totality-checking-assertions

> mutual
>   ||| free names of a process
>   fn: Eq name => (Process {name}) -> (List name)
>   fn (Sum []) = []
>   fn (Sum ((pi, P) :: rest)) = (fna pi) ++ (fn P) ++ -- issue: subtract bound names? cf. https://github.com/leithaus/rhocaml/blob/master/rho.ml#L151
>    (fn (assert_smaller (Sum ((pi, P) :: rest)) (Sum rest)))
>   fn (P | Q) = (fn P) ++ (fn Q)
>   fn (Replicated P) = fn P
>   fn (New x P) = delete x (fn P)
> 
>   ||| free names of an action
>   fna: (Action {name}) -> (List name)
>   fna (Input x y) = [x]
>   fna (Output x y) = [x, y]
> 
> mutual
>   ||| bound names of a process
>   bn: (Process {name}) -> (List name)
>   bn (Sum []) = []
>   bn (Sum ((pi, P) :: rest)) = (bna pi) ++ (bn P) ++
>    (bn (assert_smaller (Sum ((pi, P) :: rest)) (Sum rest)))
>   bn (P | Q) = (bn P) ++ (bn Q)
>   bn (Replicated P) = bn P
>   bn (New x P) = [x] ++ (bn P)
> 
>   ||| bound names of an action
>   bna: (Action {name}) -> (List name)
>   bna (Input x y) = [y]
>   bna (Output x y) = []
>
>   ||| _names_ of a process
>   n: Eq name => Process {name} -> (List name)
>   n P = (bn P) ++ (fn P)

_Yay... idris can now compute:_

```
λΠ> bn (Sum [((Output "x" "y"), zero)])
[] : List String
λΠ> fn (Sum [((Output "x" "y"), zero)])
["x", "y"] : List String
```

_next step(s): use techniques from
[rhocaml](https://github.com/leithaus/rhocaml) to define
structural equivalence and then prove the laws._

<style type="text/css">
.sourceCode { background: azure }
</style>
