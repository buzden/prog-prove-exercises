module Data.InSet.Equality

import Data.Lawful.Eqv

import Decidable.Equality

import public Syntax.WithProof

%default total

infix 6 =?=

||| Generalization of user-defined lawful equality (`Eq`, `Eqv` and `==`) and propositional equality (`DecEq` and `=`).
public export
interface Equality a where

  -- Type-level equality proofs

  EqPrf : a -> a -> Type
  NeqPrf : a -> a -> Type

  cant_eq_neq : {x, y : a} -> EqPrf x y -> NeqPrf x y -> Void

  -- Runtime equality operator

  (=?=) : (x, y : a) -> Bool

  -- Correspondence between type-level and runtime

  eq_prf_to_val : {x, y : a} -> EqPrf x y -> x =?= y = True
  eq_val_to_prf : {x, y : a} -> x =?= y = True -> EqPrf x y

  neq_prf_to_val : {x, y : a} -> NeqPrf x y -> x =?= y = False
  neq_val_to_prf : {x, y : a} -> x =?= y = False -> NeqPrf x y

  -- Properties of equality for equality operator

  equ_reflexive : (x : a) -> x =?= x = True

  equ_commutative : (x, y : a) -> x =?= y = y =?= x

  equ_transitive : (x, y, z : a) -> x =?= y = True -> y =?= z = True -> x =?= z = True

-- TODO Maybe, to split `Equality` interface to two: one for equality relation, another to equivalence properties.
--      Then, equality relation interace's implementations should be exported publicly, but properties proofs should not.

0 decEq_refl : DecEq a => (x : a) -> decEq x x = Yes Refl
decEq_refl x = case @@(decEq x x) of
  (Yes Refl ** p) => p
  (No nn ** _) => absurd $ nn Refl

trueNotFalse : Not (True = False)
trueNotFalse Refl impossible

public export
[PropositionalEq] DecEq a => Equality a where

  -- Type-level equality

  EqPrf x y = x = y
  NeqPrf x y = x = y -> Void

  cant_eq_neq xy nxy = nxy xy

  -- Value-level equality

  x =?= y = case decEq x y of
    Yes pxy => True
    No nxy => False

  -- Correspondence between type-level and runtime

  eq_prf_to_val eq_prf = rewrite eq_prf in
                         rewrite decEq_refl y in
                         Refl

  neq_prf_to_val neq_prf = case @@(decEq x y) of
    (No _ ** prf) => rewrite prf in Refl
    (Yes yy ** _) => absurd $ neq_prf yy

  eq_val_to_prf = case @@(decEq x y) of
    (Yes yy ** _) => \_ => yy
    (No _ ** prf) => rewrite prf in \ft => absurd $ trueNotFalse $ sym ft

  neq_val_to_prf = case @@(decEq x y) of
    (No nn ** _) => \_ => nn
    (Yes _ ** prf) => rewrite prf in \tf => absurd $ trueNotFalse tf

  -- Properties of value-level equality

  equ_reflexive x = rewrite decEq_refl x in Refl

  equ_commutative x y = case @@(decEq x y) of
    (Yes yy ** _) => rewrite yy in Refl
    (No _ ** no_xy) => case @@(decEq y x) of
      (Yes yy ** _) => rewrite yy in
                       rewrite decEq_refl x in
                       Refl
      (No _ ** no_yx) => rewrite no_xy in
                         rewrite no_yx in
                         Refl

  equ_transitive x y z xy yz = case (@@(decEq x y), @@(decEq y z)) of
    ((Yes eq_xy ** _), (Yes eq_yz ** _)) => rewrite eq_xy in
                                            rewrite sym eq_yz in
                                            rewrite decEq_refl y in
                                            Refl
    ((No _ ** no_xy), _) => absurd $ trueNotFalse $ sym $ rewrite sym xy in rewrite no_xy in Refl
    (_, (No _ ** no_yz)) => absurd $ trueNotFalse $ sym $ rewrite sym yz in rewrite no_yz in Refl

public export
[StandardEq] Eqv a => Equality a where

  -- Type-level equality

  EqPrf x y = x == y = True
  NeqPrf x y = x == y = False

  cant_eq_neq xy nxy = trueNotFalse rewrite sym xy in nxy

  -- Value-level equality

  x =?= y = x == y

  -- Correspondence between type-level and runtime

  eq_prf_to_val = id
  eq_val_to_prf = id

  neq_prf_to_val = id
  neq_val_to_prf = id

  -- Properties of value-level equality

  equ_reflexive x = rewrite eqvReflexive x in Refl
  equ_commutative x y = rewrite eqvCommutative x y in Refl
  equ_transitive x y z xy yz = rewrite eqvTransitive x y z xy yz in Refl
