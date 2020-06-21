module Data.InSet.Equality

import Data.Lawful.Eqv

import Decidable.Equality

import public Syntax.WithProof

%default total

public export
data EqNeq yes no = Eql yes | NotEql no

infix 6 =?=

||| Generalization of user-defined lawful equality (`Eq`, `Eqv` and `==`) and propositional equality (`DecEq` and `=`).
public export
interface Equality a where
  EqPrf : a -> a -> Type
  NeqPrf : a -> a -> Type

  cant_eq_neq : {0 x, y : a} -> EqPrf x y -> NeqPrf x y -> Void

  (=?=) : (x, y : a) -> EqNeq (EqPrf x y) (NeqPrf x y)

  equ_reflexive : (x : a) -> (equ_prf ** x =?= x = Eql equ_prf)

  equ_commutative_y : (x, y : a) -> {xy_eq : EqPrf x y} -> x =?= y = Eql xy_eq -> (yz_eq ** y =?= x = Eql yz_eq)

  equ_commutative_n : (x, y : a) -> {xy_neq : NeqPrf x y} -> x =?= y = NotEql xy_neq -> (yz_neq ** y =?= x = NotEql yz_neq)

  equ_transitive : (x, y, z : a) -> {0 xy_eq : EqPrf x y} -> {0 yz_eq : EqPrf y z} ->
                   x =?= y = Eql xy_eq -> y =?= z = Eql yz_eq -> (xz_eq ** x =?= z = Eql xz_eq)

-- TODO Maybe, to split `Equality` interface to two: one for equality relation, another to equivalence properties.
--      Then, equality relation interace's implementations should be exported publicly, but properties proofs should not.

0 decEq_refl : DecEq a => (x : a) -> decEq x x = Yes Refl
decEq_refl x = case @@(decEq x x) of
  (Yes Refl ** p) => p
  (No nn ** _) => absurd $ nn Refl

public export
[PropositionalEq] DecEq a => Equality a where
  EqPrf x y = x = y
  NeqPrf x y = x = y -> Void

  cant_eq_neq xy nxy = nxy xy

  x =?= y = case decEq x y of
    Yes pxy => Eql pxy
    No nxy => NotEql nxy

  equ_reflexive x = rewrite decEq_refl x in (Refl ** Refl)

  equ_commutative_y x y _ = rewrite xy_eq in
                            rewrite decEq_refl y in
                            (Refl ** Refl)

  equ_commutative_n x y _ = case @@(decEq y x) of
    (No n  ** nn) => rewrite nn in (n ** Refl)
    (Yes p ** _)  => absurd $ xy_neq $ sym p

  equ_transitive x y z _ _ = rewrite xy_eq in
                             rewrite yz_eq in
                             rewrite decEq_refl z in
                             (Refl ** Refl)

trueNotFalse : Not (True = False)
trueNotFalse Refl impossible

public export
[StandardEq] Eqv a => Equality a where
  EqPrf x y = x == y = True
  NeqPrf x y = x == y = False

  cant_eq_neq xy nxy = trueNotFalse rewrite sym xy in nxy

  x =?= y = case @@(x == y) of
    (True ** p) => Eql p
    (False ** n) => NotEql n

  equ_reflexive x = rewrite eqvReflexive x in (Refl ** rewrite eqvReflexive x in Refl)

  equ_commutative_y x y _ = rewrite eqvCommutative y x in
                            rewrite xy_eq in
                            (Refl ** rewrite eqvCommutative y x in rewrite xy_eq in Refl)

  equ_commutative_n x y xy = rewrite eqvCommutative y x in
                             (xy_neq ** rewrite sym xy in rewrite xy_neq in rewrite eqvCommutative y x in Refl)

  equ_transitive x y z xy yz = rewrite eqvTransitive x y z xy_eq yz_eq in (Refl ** rewrite eqvTransitive x y z xy_eq yz_eq in Refl)
