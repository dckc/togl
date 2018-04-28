Toward $\pi$-calculus in idris
==============================

We're transcribing/implementing ...

* Milner, Robin. _[The polyadic π-calculus: a tutorial.][RM93]_
  In Logic and algebra of specification, pp. 203-246.
  Springer, Berlin, Heidelberg, 1993.

[RM93]: https://pdfs.semanticscholar.org/5d25/0a3a14f68abb1ae0111d35b8220b4472b277.pdf

> module picalc2
> 
> %access export

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

> mutual
>   ||| Processes are built from names ...
>   data Process : {name: Type} -> Type where

The summation form represents a process able to take part in one --
but only one -- of several alternatives for communication.

>     Sum: (List (Action {name}, Process {name})) -> Process {name}

$P | Q$ -- "$P$ par $Q$" -- simply means that $P$ and $Q$ are
concurrently active.

>     Par: (P: Process {name}) -> (Q: Process {name}) -> Process {name}

$!P$ -- "bang $P$" means $P|P|...$ as many copies as you wish.

>     
>     Replication: (P: Process {name}) -> Process {name}

$(\nu x)P$ -- "new $x$ in $P$" -- restricts the use of the name $x$ to $P$. 

>     New: (x: name) -> (P: Process {name}) -> Process {name}


In a summand $\pi.P$ the prefix $\pi$ represents an _atomic action_,
the first action performed by $\pi.P$. There are two basic forms of
prefix:

>   data Action : {name: Type} -> Type where

 - $x(y)$, which binds $y$ in the prefix process, means
   "input some name -- call it $y$ -- along the link named $x$"

>     Input: (x: name) -> (y: name) -> Action {name}

 - $\bar{x}y$ , which does not bind $y$, means "output the name $y$
   along the link named $x$".

>     Output: (xbar: name) -> (y: name) -> Action {name}
>

In the case $I = \emptyset$, we write the sum as $0$.

> zero: Process
> zero = Sum []

We call $x$ the _subject_ ...

> subject: Action {name} -> name
> subject (Input x y) = x
> subject (Output xbar y) = xbar

We call ... $y$ the _object_

> object: Action {name} -> name
> object (Input x y) = y
> object (Output xbar y) = y
