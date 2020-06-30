module Chapter4

import Chapter3

import Data.Bool
import Data.InSet
import Data.InSet.List
import Data.List
import Data.List.Equalities

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

falseNotTrue : Not (False = True)
falseNotTrue Refl impossible

namespace Exercise_4_6

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

replicate_appended : (n : Nat) -> (x : a) -> (w : List a) -> replicate n x ++ x::w = x :: replicate n x ++ w
replicate_appended 0     x w = Refl
replicate_appended (S n) x w = rewrite replicate_appended n x w in Refl

list_splits : (u, v, x, y : List a) -> u ++ v = x ++ y -> Either (m ** (u = x ++ m, y = m ++ v)) (m ** (x = u ++ m, v = m ++ y))
list_splits [] _ x  _ prf = Right (x ** (Refl, prf))
list_splits u  _ [] _ prf = Left  (u ** (Refl, sym prf))
list_splits (_::us) v (_::xs) y prf = rewrite fst $ consInjective prf in
                                      case list_splits us v xs y $ snd $ consInjective prf of
                                        Right (m ** (ux, vy)) => rewrite ux in Right (m ** (Refl, vy))
                                        Left  (m ** (ux, vy)) => rewrite ux in Left  (m ** (Refl, vy))

append_is_nil : (l, r : List a) -> l ++ r = [] -> (l = [], r = [])
append_is_nil [] [] Refl = (Refl, Refl)

append_is_singleton : (l, r : List a) -> (x : a) -> [x] = l ++ r -> Either (l = [x], r = []) (l = [], r = [x])
append_is_singleton [] [x] x Refl = Right (Refl, Refl)
append_is_singleton [x] [] x Refl = Left (Refl, Refl)
append_is_singleton [_] (_::_) _ Refl impossible
append_is_singleton (_::_::_) _ _ Refl impossible

analyze_s : S lr -> Either (lr = []) $
                    Either (w ** sw : S w ** lr = [A] ++ w ++ [B])
                           (w ** v ** sw : S w ** sv : S v ** lr = w ++ v)
analyze_s Empty = Left Refl
analyze_s (Asb {w} sw) = Right $ Left (w ** sw ** Refl)
analyze_s (Ss {w} {v} sw sv) = Right $ Right (w ** v ** sw ** sv ** Refl)

s_can_insert_ab : (l, r : List Alpha) -> S (l ++ r) -> S (l ++ [A, B] ++ r)
s_can_insert_ab l r s = case analyze_s s of
                          Left lr_nil => rewrite fst $ append_is_nil l r lr_nil in
                                         rewrite snd $ append_is_nil l r lr_nil in
                                         Asb Empty
                          Right $ Left (w ** sw ** eq) =>
                            case list_splits l r [A] (w ++ [B]) eq of
                              Left (m ** (l_Am, wB_mr)) => rewrite l_Am in case list_splits m r w [B] $ sym wB_mr of
                                Left (k ** (m_wk, kr)) => rewrite m_wk in case append_is_singleton k r B kr of
                                  Left  (kB, rn) => rewrite kB in
                                                    rewrite rn in
                                                    Ss (Asb sw) (Asb Empty)
                                  Right (kn, rB) => rewrite kn in
                                                    rewrite rB in
                                                    rewrite appendNilRightNeutral w in
                                                    rewrite appendAssociative w [A, B] [B] in
                                                    Asb $ Ss sw $ Asb Empty
                                Right (k ** (w_mk, r_kB)) =>
                                  rewrite r_kB in
                                  rewrite appendAssociative m (A::B::k) [B] in
                                  Asb $ s_can_insert_ab (assert_smaller l m) (assert_smaller r k) rewrite sym w_mk in sw
                              Right (m ** (lm, r_mwB)) => rewrite r_mwB in case append_is_singleton l m A lm of
                                Left (lA, mn) => rewrite lA in
                                                 rewrite mn in
                                                 Asb $ Ss (Asb Empty) sw
                                Right (ln, mA) => rewrite ln in
                                                  rewrite mA in
                                                  rewrite sym eq in
                                                  Ss (Asb Empty) s
                          Right $ Right (w ** v ** sw ** sv ** eq) => case list_splits l r w v eq of
                            Left (m ** (l_wm, v_rm)) =>
                              rewrite l_wm in
                              rewrite sym $ appendAssociative w m (A::B::r) in
                              Ss sw $ s_can_insert_ab (assert_smaller l m) r rewrite sym v_rm in sv
                            Right (m ** (w_lm, r_mv)) =>
                              rewrite r_mv in
                              rewrite appendAssociative l (A::B::m) v in
                              flip Ss sv $ s_can_insert_ab l (assert_smaller r m) rewrite sym w_lm in sw

s_can_elim_ab : (l, r : List Alpha) -> S (l ++ [A, B] ++ r) -> S (l ++ r)
s_can_elim_ab l r s = case analyze_s s of
                        Left eq => ?s_can_elim_ab_rhs_1
                        Right $ Left (w ** sw ** eq) => ?s_can_elim_ab_rhs_2
                        Right $ Right (w ** v ** sw ** sv ** eq) => ?s_can_elim_ab_rhs_3

balanced_appended : (n : Nat) -> (l, r : List Alpha) -> balanced n l = True -> balanced 0 r = True -> balanced n (l ++ r) = True
balanced_appended 0      []    _ _   prf = prf
balanced_appended 0     (A::l) r plf prf = balanced_appended 1 l r plf prf
balanced_appended (S n) (A::l) r plf prf = balanced_appended (S $ S n) l r plf prf
balanced_appended (S n) (B::l) r plf prf = balanced_appended n l r plf prf

-- There are a four statements instead of one because `balanced` is coded with `Bool` but `S.S` is inductive data type.

export
balanced_true_as_s : (n : Nat) -> (w : List Alpha) -> balanced n w = True -> S.S $ replicate n A ++ w
balanced_true_as_s 0     []     _   = Empty
balanced_true_as_s 0     (A::w) prf = balanced_true_as_s 1 w prf
balanced_true_as_s (S n) (A::w) prf = rewrite appendAssociative (replicate (S n) A) [A] w in
                                      rewrite replicate_appended n A [] in
                                      rewrite appendNilRightNeutral $ replicate n A in
                                      balanced_true_as_s (2 + n) w prf
balanced_true_as_s (S n) (B::w) prf = rewrite sym $ replicate_appended n A (B::w) in
                                      s_can_insert_ab (replicate n A) w $ balanced_true_as_s n w prf

export
s_as_balanced_true : (n : Nat) -> (w : List Alpha) -> S.S $ replicate n A ++ w -> balanced n w = True
s_as_balanced_true 0 [] Empty = Refl
s_as_balanced_true 0 (A :: w ++ [B]) (Asb x) = s_as_balanced_true 1 (w ++ [B]) (Asb x)
s_as_balanced_true 0 (w ++ v) (Ss x y) = let xx = assert_total $ s_as_balanced_true 0 w x in
                                         let yy = assert_total $ s_as_balanced_true 0 v y in
                                         balanced_appended 0 w v xx yy
s_as_balanced_true (S n) [] Empty impossible
s_as_balanced_true (S n) (A::w) x = s_as_balanced_true (S $ S n) w rewrite sym $ replicate_appended n A w in x
s_as_balanced_true (S n) (B::w) x = s_as_balanced_true n w $ s_can_elim_ab (replicate n A) w rewrite replicate_appended n A (B::w) in x

export
balanced_false_as_not_s : (n : Nat) -> (w : List Alpha) -> balanced n w = False -> Not $ S.S $ replicate n A ++ w
balanced_false_as_not_s n w prf s = falseNotTrue $ rewrite sym prf in s_as_balanced_true n w s

export
not_s_as_balanced_false : (n : Nat) -> (w : List Alpha) -> Not $ S.S $ replicate n A ++ w -> balanced n w = False
not_s_as_balanced_false n w f = case decEq (balanced n w) False of
  Yes p => p
  No no => absurd $ f $ balanced_true_as_s n w $ notFalseIsTrue no
