module RhoCalculus

{-
A Reflective Higher-order Calculus
L.G.Meredith MatthiasRadestock
Electronic Notes in Theoretical Computer Science
Volume 141, Issue 5, 22 December 2005, Pages 49-67
http://www.sciencedirect.com/science/article/pii/S1571066105051839
-}

mutual
  data Process: Type where
    Null: Process
    Input: (x, y: Name) -> (P: Process) -> Process
    Lift: (x: Name) -> (P: Process) -> Process
    Drop: (x: Name) -> Process
    Parallel: (P: Process) -> (Q: Process) -> Process

  data Name: Type where
    Quote: (P: Process) -> Name

syntax [x] "[" [y] "]" = output x y
output : Name -> Name -> Process
output x y = Lift x $ Drop y

exampleName: Name
exampleName = Quote Null

twoNewProcesses: List Process
twoNewProcesses =
  [qz[qz],
   Input qz qz Null]
 where
   qz = Quote Null

moreNames: List Name
moreNames = map Quote twoNewProcesses
