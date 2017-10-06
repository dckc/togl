module Graph

import Data.List
import Data.List.Quantifiers

-- Notes on a theory of graphs
-- Greg Meredith
-- https://stackedit.io/editor#!provider=couchdb&id=UdUSSGCZgNDxSIPYmMfoX5Kk

Disjoint : (xs, ys : List a) -> Type
Disjoint xs ys = All (\y => Not (Elem y xs)) ys

-- TODO: nicer syntax; maybe even dsl block
-- ISSUE: x, v have to be Dec

data GraphExpression : (x: Type) -> (v: Type) -> Type where
  Empty : GraphExpression x v
  Adjoin : (Either x v) -> (g: (GraphExpression x v)) -> (GraphExpression x v)
  Juxtapose : (GraphExpression x v) -> (GraphExpression x v) -> (GraphExpression x v)
  Let : x -> v -> (GraphExpression x v) -> (GraphExpression x v)
  Connect : x -> v -> (GraphExpression x v) -> x -> v -> (GraphExpression x v) -> (GraphExpression x v)

data AdmissibleVertex : {x: Type} -> {v: Type}
  -> (gxv: (GraphExpression x v))
  -> (gamma: List x)
  -> v -> Type
  where
  Verticity : (vv : v) -> AdmissibleVertex gxv [] vv


data AdmissibleVariable : {x: Type} -> {v: Type}
  -> (gxv: (GraphExpression x v))
  -> (gamma: List x)
  -> x -> Type
  where
  -- what is \emptyset doing in Variation? Why not ()?
  Variation : (xx : x) -> AdmissibleVariable gxv [] xx


data WellFormed : {x: Type} -> {v: Type}
  -> (gxv: (GraphExpression x v))
  -> (gamma: (List x))
  -> (GraphExpression x v) -> Type
  where
  Foundation : WellFormed gxv [] Empty
  Participation : (WellFormed gxv gamma g) -> (AdmissibleVertex gxv [] vv)
    -> WellFormed gxv gamma (Adjoin (Right vv) g)
  Dependence :(WellFormed gxv gamma g) -> (AdmissibleVariable gxv [] xx)
    -> WellFormed gxv gamma (Adjoin (Left xx) g)
  Juxtaposition : { gamma12: List x }
    -> {auto cat : gamma12 = (gamma1 ++ gamma2)} -- work-around?
    -> {auto disjoint : Disjoint gamma1 gamma2 }
    -> (WellFormed gxv gamma1 g1) -> (WellFormed gxv gamma2 g2)
    -> WellFormed gxv gamma12 (Juxtapose g1 g2)
  Nomination :
       (WellFormed gxv gamma g) -> (AdmissibleVariable gxv [] xx)
    -> WellFormed gxv gamma (Let x v g)
  Connection : { gamma12: List x }
    -> {auto disjoint: Disjoint gamma1 gamma2 }
    -> {auto cat : gamma12 = (gamma1 ++ gamma2)} -- work-around?
    -> WellFormed gxv gamma1 (Let x1 v1 g1)
    -> WellFormed gxv gamma2 (Let x2 v2 g2)
    -> WellFormed gxv gamma12 (Connect x1 v1 g1 x2 v2 g2)
