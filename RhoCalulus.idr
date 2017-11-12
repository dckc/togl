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

-- syntax [x] "[" [y] "]" = output x y
output : Name -> Name -> Process
output x y = Lift x $ Drop y

exampleName: Name
exampleName = Quote Null

twoNewProcesses: List Process
twoNewProcesses =
  [output qz qz,
   Input qz qz Null]
 where
   qz = Quote Null

moreNames: List Name
moreNames = map Quote twoNewProcesses

freeNames: Process -> List Name
freeNames Null = []
freeNames (Input x y P) = union [x] (delete y (freeNames P))

mutual
  data CongP: Process -> Process -> Type where
    Alpha: AlphaP P Q -> CongP P Q
    NeutralL: CongP (Parallel P Null) P
    NeutralR: CongP (Parallel Null P) P
    CommuteProc: CongP (Parallel P Q) (Parallel Q P)
    AssocProc: CongP (Parallel (Parallel P Q) R) (Parallel P (Parallel Q R))
  data EquivN: Name -> Name -> Type where
    QuoteDrop: EquivN (Quote $ Drop x) x
    StructEquiv: (CongP P Q) -> EquivN (Quote P) (Quote Q)
  substP: Process -> (Name, Name) -> Process
  substP Null s = Null
  substP (Parallel R S) s = Parallel (substP R s) (substP S s)
  substP (Input x y R) (nQ, nP) =
    Input (substN x s) z (subst (subst R (z, y)) (nQ, nP))
    where
      z = (skolem [nQ, nP] ++ (freeNames Q) ++ (names R))
      skolem names = ?hole
      names x = ?hole2
  substP (Lift x R) s = Lift (substN x s) (substP R s)
  substP (Drop x) s = Drop x {- TODO: EquivName Yes / No -}
  substN: Name -> (Name, Name) -> Name
  substN n s = n {- TODO: EquivName Yes / No -}
