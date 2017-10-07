module Graph

import Data.List
import Data.List.Quantifiers

-- Notes on a theory of graphs
-- Greg Meredith
-- https://stackedit.io/editor#!provider=couchdb&id=UdUSSGCZgNDxSIPYmMfoX5Kk

%default total

Disjoint : (xs, ys : List a) -> Type
Disjoint xs ys = All (\y => Not (Elem y xs)) ys

-- TODO: nicer syntax; maybe even dsl block
-- ISSUE: x, v have to be Dec

syntax GG "[" [x] "," [v] "]" ";" [gamma] "|-" [g]  = WellFormed x v gamma g;
syntax G  "[" [x] "," [v] "]"                       = GraphExpression x v;

data GraphExpression : (x: Type) -> (v: Type) -> Type where
  Empty : G[x, v]
  Adjoin : v -> G[x, v] -> G[x, v]
  AdjoinX : x -> G[x, v] -> G[x, v]
  Juxtapose : G[x, v] -> G[x, v] -> G[x, v]
  Let : x -> v -> G[x, v] -> G[x, v]
  Connect : x -> v -> G[x, v] -> x -> v -> G[x, v] -> G[x, v]

syntax [v] "|" [g]                 = Adjoin v g;
syntax [x] "/" [g]                 = AdjoinX x g; -- hmm..
syntax [g1] ":*:" [g2]             = Juxtapose g1 g2;
syntax "let" [x] "=" [v] "in" [g]  = Let x v g;
syntax "<" "let" [x1] "=" [v1] "in" [g1] "," "let" [x2] "=" [v2] "in" [g2] ">" = Connect x1 v1 g1 x2 v2 g2;

syntax GV "[" [x] "," [v] "]" ";" [gamma] "|-" [v'] = AdmissibleVertex x v gamma v';

data AdmissibleVertex : (x, v: Type) -> (List x) -> v -> Type where
  Verticity : {v': v} -> (GV[x, v] ; [] |- v')


syntax GX "[" [xx] "," [vv] "]" ";" [gamma] "|-" [x] = AdmissibleVariable xx vv gamma x;

data AdmissibleVariable : (x, v: Type) -> (List x) -> x -> Type where
  -- what is \emptyset doing in Variation? Why not ()?
  Variation : {x': x} -> (GX[x, v] ; [] |- x')

data WellFormed : (x, v: Type) -> (List x) -> G[x, v] -> Type where
  Foundation : GG[x, v] ; [] |- Empty
  Participation : (GG[x, v] ; gamma |- g) -> (GV[x, v] ; [] |- v')
    -> GG[x, v] ; gamma |- (v' | g)
  Dependence :(GG[x, v] ; gamma |- g) -> (GX[x, v] ; [] |- x')
    -> GG[x, v] ; gamma |- (x' / g)
  Juxtaposition : {auto disjoint: Disjoint gamma1 gamma2 }
    -> (GG[x, v]; gamma1 |- g1) -> (GG[x, v]; gamma2 |- g2)
    -> GG[x, v]; (gamma1 ++ gamma2) |- (g1 :*: g2)
  Nomination :
       (GG[x, v]; (x' :: gamma) |- g) -> (GV[x, v]; [] |- v')
    -> GG[x, v]; gamma |- (let x' = v' in g)
  Connection : {auto disjoint: Disjoint gamma1 gamma2 }
    -> (GG[x, v]; gamma1 |- (let x1 = v1 in g1))
    -> (GG[x, v]; gamma2 |- (let x2 = v2 in g2))
    -> (GG[x, v]; (gamma1 ++ gamma2) |- (<let x1 = v1 in g1, let x2 = v2 in g2>))

syntax GE "[" [x] "," [v] "]" "|-" [v'] "in" [g] = Membership x v v' g;

data Membership: (x, v: Type) -> (v': v) -> G[x, v] -> Type where
  Ground: GE[x, v] |- v' in (v' | g)
  Union: (GE[x, v] |- v' in g)
    -> GE[x, v] |- v' in (g :*: g')
  Transparency: (GE[x, v] |- v' in g)
    -> GE[x, v] |- v' in (let x' = v' in g)
  Link_L: (GE[x, v] |- v' in g_1)
    -> GE[x, v] |- v' in (<let x_1 = v_1 in g_1, let x_2 = v_2 in g_2>)
  Link_R: (GE[x, v] |- v' in g_2)
    -> GE[x, v] |- v' in (<let x_1 = v_1 in g_1, let x_2 = v_2 in g_2>)


-- hmm... can we absorb, rather than reify, some of these |-s?
syntax GI "[" [x] "," [v] "]" "|-" [g1] "=" [g2] = Equiv x v g1 g2

data Equiv: (x, v: Type) -> G[x, v] -> G[x, v] -> Type where
  Identity: GI[x, v] |- (Empty :*: g) = g
  Symmetry: GI[x, v] |- (g1 :*: g2) = (g2 :*: g1)
  Associativity: GI[x, v] |- (g1 :*: (g2 :*: g3)) = ((g1 :*: g2) :*: g3)
  Permutation:  GI[x, v] |- (v1 | (vi | (vj | g))) = (v1 | (vj | (vi | g)))
  Conservation: GI[x, v] |- (Let xx vv (Let x' vv g)) = (Let xx vv g)
{- issue: variables / terms
  Extrusion: (Not (GE[x, v] |- xx in g2))
    -> GI[x, v] |- ((Let xx vv g1) :*: g2) = (Let xx vv (g1 :*: g2))
-}

discrete : Nat -> G[x, Nat]
discrete Z = Empty
discrete (S n_1) = (n | Empty) :*: (discrete n_1)
  where n = S n_1

connect' : G[x, v] -> G[x, v] -> G[x, v]
connect' (Let x1 v1 g1) (Let x2 v2 g2) = Connect x1 v1 g1 x2 v2 g2
connect' _ _ = Empty

chain : Nat -> G[Nat, Nat]
chain Z = Empty
chain (S Z) = Let 2 1 (1|Empty)
chain (S n_1) =
 Let (2 * n) n (connect' (let ((2 * (S n_1)) - 1) = n in (n|Empty))
                         (chain n_1))
   where n = S n_1

cycle : Nat -> G[Nat, Nat]
cycle Z = Empty
cycle (S k) = connect' (chain (S k)) (chain (S Z))
