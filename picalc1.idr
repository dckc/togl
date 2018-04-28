{-
2 The Monadic pi-calculus

https://pdfs.semanticscholar.org/5d25/0a3a14f68abb1ae0111d35b8220b4472b277.pdf
-}

data Action : {name: Type} -> Type where
  Null: Action {name}
  Input: (x: name) -> (y: name) -> Action {name}
  Output: (xbar: name) -> (y: name) -> Action {name}

data Process : {name: Type} -> Type where
  Sum: (Pi: List (Action {name})) -> Process {name}
  Par: (P: Process {name}) -> (Q: Process {name}) -> Process {name}
  Replication: (P: Process {name}) -> Process {name}
  New: (x: name) -> (P: Process {name}) -> Process {name}
{-
typo?

Note that R has become yv or zv;

should be:

Note that Q has become yv or zv;

no?
-}

%default total

fna: (Action {name}) -> (List name)
fna Null = []
fna (Input x y) = [x]
fna (Output xbar y) = [xbar, y]

fn: Eq name => (Process {name}) -> (List name)
fn (Sum []) = []
fn (Sum (a :: as)) = (fna a) ++
 (fn (assert_smaller (Sum (a :: as)) (Sum as)))
fn (Par P Q) = (fn P) ++ (fn Q)
fn (Replication P) = fn P
fn (New x P) = delete x (fn P)
