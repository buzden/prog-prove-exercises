module Data.InSet.Equality

import Data.Lawful.Eqv

import Decidable.Equality

import Syntax.WithProof

%default total

public export
data EqNeq yes no = Eql yes | NotEql no

infix 6 =?=

||| Generalization of user-defined lawful equality (`Eq`, `Eqv` and `==`) and propositional equality (`DecEq` and `=`).
public export
interface Equality a where
  EqPrf : a -> a -> Type
  NeqPrf : a -> a -> Type

  (=?=) : (x, y : a) -> EqNeq (EqPrf x y) (NeqPrf x y)

  equ_reflexive : (x : a) -> (equ_prf ** x =?= x = Eql equ_prf)

  equ_commutative_y : (x, y : a) -> {xy_eq : EqPrf x y} -> x =?= y = Eql xy_eq -> (yz_eq ** y =?= x = Eql yz_eq)

  equ_commutative_n : (x, y : a) -> {xy_neq : NeqPrf x y} -> x =?= y = NotEql xy_neq -> (yz_neq ** y =?= x = NotEql yz_neq)

  equ_transitive : (x, y, z : a) -> {0 xy_eq : EqPrf x y} -> {0 yz_eq : EqPrf y z} ->
                   x =?= y = Eql xy_eq -> y =?= z = Eql yz_eq -> (xz_eq ** x =?= z = Eql xz_eq)

0 decEq_refl : DecEq a => (x : a) -> decEq x x = Yes Refl
decEq_refl x = case @@(decEq x x) of
  (Yes Refl ** p) => p
  (No nn ** _) => absurd $ nn Refl

public export
[PropositionalEq] DecEq a => Equality a where
  EqPrf x y = x = y
  NeqPrf x y = x = y -> Void

  x =?= y = case decEq x y of
    Yes pxy => Eql pxy
    No nxy => NotEql nxy

  equ_reflexive x = rewrite decEq_refl x in (Refl ** Refl)

  equ_commutative_y x y xy = rewrite xy_eq in
                             rewrite decEq_refl y in
                             (Refl ** Refl)

  equ_commutative_n x y _ = case @@(decEq y x) of
    (No n  ** nn) => rewrite nn in (n ** Refl)
    (Yes p ** _)  => absurd $ xy_neq $ sym p

  equ_transitive x y z xy yz = rewrite xy_eq in
                               rewrite yz_eq in
                               rewrite decEq_refl z in
                               (Refl ** Refl)

public export
[StandardEq] Eqv a => Equality a where
  EqPrf x y = x == y = True
  NeqPrf x y = x == y = False

  x =?= y = case @@(x == y) of
    (True ** p) => Eql p
    (False ** n) => NotEql n

  equ_reflexive x = ?refl_rhs

  equ_commutative_y = ?comm_rhs_y

  equ_commutative_n = ?comm_rhs_n

  equ_transitive = ?trans_rhs
