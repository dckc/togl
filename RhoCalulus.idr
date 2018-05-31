module RhoCalculus

{-
A Reflective Higher-order Calculus
L.G.Meredith MatthiasRadestock
Electronic Notes in Theoretical Computer Science
Volume 141, Issue 5, 22 December 2005, Pages 49-67
http://www.sciencedirect.com/science/article/pii/S1571066105051839
-}

%access export
%default total

mutual
  data Process: Type where
    Zero: Process
    Input: Action -> (P: Process) -> Process
    Lift: (x: Name) -> (P: Process) -> Process
    Drop: (x: Name) -> Process
    Par: (List Process) -> Process

  data Action: Type where
    Act: (x: Name) -> (y: Name) -> Action

  data Name: Type where
    Quote: (P: Process) -> Name

zero: Process
zero = Zero

guard: Name -> Name -> Action
guard nsubj nobj = Act nsubj nobj

input: Name -> Name -> Process -> Process
input nsubj nobj cont = Input (Act nsubj nobj) cont

prefix_: Action -> Process -> Process
prefix_ (Act (Quote proc1) (Quote proc2)) cont = Input (Act (Quote proc1) (Quote proc2)) cont

lift: Name -> Process -> Process
lift nsubj cont = Lift nsubj cont

drop: Name -> Process
drop n = Drop n

par: Process -> Process -> Process
par (Par proclist1) (Par proclist2) = Par (proclist1 ++ proclist2)
par (Par proclist) proc = Par (proclist ++ [proc])
par proc (Par proclist) = Par ([proc] ++ proclist)
par p1 p2 = Par [p1, p2]

parstar: List Process -> Process
parstar [] = Zero
parstar (proclisthd :: proclisttl) = foldl par proclisthd proclisttl

quote : Process -> Name
quote proc = Quote proc

mutual
  processQuoteDepth: Process -> Nat  -- TODO: prove totality
  processQuoteDepth Zero = 0
  processQuoteDepth (Input (Act nsubj nobj) cont) =
    maximum (nameQuoteDepth nsubj) (processQuoteDepth cont)
  processQuoteDepth (Lift nsubj cont) =
    maximum (nameQuoteDepth nsubj) (processQuoteDepth cont)
  processQuoteDepth (Drop n) = nameQuoteDepth n
  processQuoteDepth (Par procs) =
   assert_total $ foldl (\qD, proc => maximum qD (processQuoteDepth proc))
         0
         procs

  nameQuoteDepth: Name -> Nat
  nameQuoteDepth (Quote proc) = assert_total $ 1 + (processQuoteDepth proc)

syntax [x] "[" [y] "]" = output x y
output : Name -> Name -> Process
output x y = Lift x $ Drop y

exampleName: Name
exampleName = Quote Zero

twoNewProcesses: List Process
twoNewProcesses =
  [qz[qz],
   Input (Act qz qz) Zero]
 where
   qz = Quote Zero

moreNames: List Name
moreNames = map Quote twoNewProcesses
