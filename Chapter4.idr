module Chapter4

import Chapter3

import Data.InSet
import Data.InSet.List
import Data.List

import Decidable.Equality

%default total

-- Section 4.1 --

public export
data Surj : (f : a -> b) -> Type where
  SurjPrf : ((x : a) -> (y ** x = f y)) -> Surj f

export
to_list_not_surj : Not $ (f : a -> List a) -> Surj f
to_list_not_surj surj = let SurjPrf f = surj \x => [x] in
                        let (y ** prf) = f [] in
                        lemma_val_not_nil $ sym prf

public export
EqRefl : Type -> Type
EqRefl a = Eq a => (x : a) -> x == x = True

export
to_set_not_surj : Equality a => EqRefl a -> Not $ (f : a -> InSet a) -> Surj f
to_set_not_surj er surj = let SurjPrf f = surj \x => [x] in
                          let (y ** prf) = f [] in
                          non_empty_is_not_empty (y ** x_in_x_etc y []) $ sym prf

-- Exercise 4.1 --

export
lemma_4_1 : {t, a : ty -> ty -> Type} ->
            (T : (x, y : ty) -> Either (t x y) (t y x)) ->
            (A : (x, y : ty) -> a x y -> a y x -> x = y) ->
            (TA : (x, y : ty) -> t x y -> a x y) ->
            {x, y : ty} -> a x y -> t x y
lemma_4_1 tl al tal axy = case tl x y of
  Left  txy => txy
  Right tyx => rewrite al x y axy $ tal y x tyx in either id id $ tl y y

  -- Alternatively, you can write a proof without usage of `tl y y`:
  --Right tyx => let u = al x y axy $ tal y x tyx in
  --             rewrite u in
  --             rewrite cong (t y) $ sym u in
  --             tyx

-- Exercise 4.2 --

length_of_init : (x : a) -> (xs : List a) -> length (init $ x::xs) = length xs
length_of_init _ []      = Refl
length_of_init _ (x::xs) = rewrite length_of_init x xs in Refl

last_goes_right : (x : a) -> (xs, ys : List a) -> init (x::xs) ++ last (x::xs)::ys = x::xs ++ ys
last_goes_right _ []      _  = Refl
last_goes_right _ (x::xs) ys = rewrite last_goes_right x xs ys in Refl

export
lemma_4_2 : (xs : List a) -> (ys ** zs ** (xs = ys ++ zs, Either (length ys = length zs) (length ys = 1 + length zs)))
lemma_4_2 [] = ([] ** [] ** (Refl, Left Refl))
lemma_4_2 (x::xs) = let (ys ** zs ** (xyz, lengths)) = lemma_4_2 xs in
                    rewrite xyz in
                    case lengths of
                      Left yz => (x::ys ** zs ** rewrite yz in (Refl, Right Refl))
                      Right ySz => let (yh::ytl) = ys in
                                   (x :: init ys ** last ys :: zs ** rewrite length_of_init x ys in
                                                                     rewrite ySz in
                                                                     rewrite last_goes_right yh ytl zs in
                                                                     (Refl, Left Refl))

  -- I did the proof of ex. 4.2 by case analysis rather than by suggesting `take (half $ 1 + length xs) xs` and `drop (half $ 1 + length xs) xs` as
  -- `ys` and `zs` respectively because this solution is simpler for Idris since it does not involve `Nat` division and other arithmetics.
  -- Standard library also seems to not to contain lemmas about `take` and `drop`, thus I need to formulate and prove them myself.
  -- It is possible, but tough.

-- Section 4.4.6 --

export
not_ev_3 : Not $ Ev 3
not_ev_3 (EvSS _) impossible

export
ev_suc_thus_not : Ev (S m) -> Not $ Ev m
ev_suc_thus_not (EvSS x) (EvSS y) = ev_suc_thus_not x y

-- Exercise 4.3 --

export
ev_ss_thus_ev : Ev (S $ S n) -> Ev n
ev_ss_thus_ev (EvSS x) = x

-- Exercise 4.4 --

-- Look to `not_ev_3` above. Solution is the same since there's no special method for __rule inversion__.

-- Exercise 4.5 --

-- Well, the solution is the same as in the chapter 3:
--iter_then_star : Iter r n x y -> Star r x y
--iter_then_star IterZ       = Refl
--iter_then_star (IterS x z) = Step x (iter_then_star z)

-- Exercise 4.6 --

-- `elems` is defined in `Data.InSet.List`.

namespace Exercise_4_6

  falseNotTrue : Not (False = True)
  falseNotTrue Refl impossible

  export %hint %inline
  UsedEquality : DecEq a => Equality a
  UsedEquality = PropositionalEq

  export
  list_splits : DecEq a => (xs : List a) -> (x : a) -> (x `isin` elems xs = True) -> (ys ** zs ** (xs = ys ++ x :: zs, x `isin` elems ys = False))
  list_splits [] x prf = absurd $ falseNotTrue rewrite sym $ not_in_empty x in prf
  list_splits (y::ys) x prf = case @@(x =?= y) of
    (True  ** p) => ([] ** ys ** (rewrite eq_val_to_prf {x} {y} @{PropositionalEq} p in Refl
                                , rewrite not_in_empty x in Refl))
    (False ** p) => let (subl ** subr ** (eq, f)) = list_splits ys x (is_in_tail x y (elems ys) p prf) in
                    (y::subl ** subr ** (rewrite eq in Refl, not_in_both x y (elems subl) p f))

-- Exercise 4.7 --

public export
balanced : Nat -> List Alpha -> Bool
balanced 0     []     = True
balanced n     (A::w) = balanced (S n) w
balanced (S n) (B::w) = balanced n w
balanced _     _      = False

-- There are a four statements instead of one because `balanced` is coded with `Bool` but `S.S` is inductive data type.

export
balanced_true_as_s : (n : Nat) -> (w : List Alpha) -> balanced n w = True -> S.S $ replicate n A ++ w

export
balanced_false_as_not_s : (n : Nat) -> (w : List Alpha) -> balanced n w = False -> Not $ S.S $ replicate n A ++ w

export
s_as_balanced_true : (n : Nat) -> (w : List Alpha) -> S.S $ replicate n A ++ w -> balanced n w = True

export
not_s_as_balanced_false : (n : Nat) -> (w : List Alpha) -> Not $ S.S $ replicate n A ++ w -> balanced n w = False
