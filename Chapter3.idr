module Chapter3

import Data.Bool
import Data.InSet
import Data.List
import Data.Nat
import Data.So
import Decidable.Equality

%default total

-- Exercise 3.1

public export
data Tree a = Tip
            | Node (Tree a) a (Tree a)

public export
set : Eq a => Tree a -> InSet a
set Tip          = []
set (Node l x r) = [x] + set l + set r

public export
all_satisfy : (a -> Bool) -> Tree a -> Bool
all_satisfy _ Tip          = True
all_satisfy p (Node l x r) = p x && all_satisfy p l && all_satisfy p r

public export
ord : Ord a => Tree a -> Bool
ord Tip = True
ord (Node l x r) = ord l && ord r && all_satisfy (<= x) l && all_satisfy (>= x) r

public export
ins : Ord a => a -> Tree a -> Tree a
ins n Tip = Node Tip n Tip
ins n t@(Node l x r) with (x == n)
  ins n t@(Node _ _ _) | True = t
  ins n t@(Node l x r) | False with (x < n)
    ins n t@(Node l x r) | False | True  = Node (ins n l) x r
    ins n t@(Node l x r) | False | False = Node l x (ins n r)

export
ins_adds : Ord a => (n : a) -> (t : Tree a) -> set (ins n t) == [n] + set t
ins_adds n Tip p = let u = union_empty_neutral ([n] + []) p in
                   rewrite u in -- what's the f**k? why should I do this?
                   rewrite union_empty_neutral [n] p in
                   Refl
ins_adds n (Node l x r) p with (x == n)
  ins_adds n (Node l x r) p | True =
                                     --rewrite sym $ eq_appended_eq ([x] + set l + set r) xn_eq p in
                                     ?ins_adds_rhs_1
  ins_adds n (Node l x r) p | False with (x < n)
    ins_adds n (Node l x r) p | False | True =
                                               rewrite sym $ union_associative [x] (set (ins n l)) (set r) p in
                                               let v = union_eq_cong_l (set r) (ins_adds n l) in
                                               let u = union_eq_cong_r [x] v p in
                                               --rewrite u p in
                                               ?ins_adds_rhs_2
    ins_adds n (Node l x r) p | False | False = ?ins_adds_rhs_3

export
ins_preserves_ord : Ord a => (i : a) -> (t : Tree a) -> ord t = True -> ord (ins i t) = True

-- Examples from section 3.5.1

public export
data Ev : Nat -> Type where
  Ev0  : Ev 0
  EvSS : Ev n -> Ev (S $ S n)

export
ev4 : Ev 4
ev4 = EvSS (EvSS Ev0)

public export
evn : Nat -> Bool
evn Z         = True
evn (S Z)     = False
evn (S (S n)) = evn n

export
ev_thus_evn_true : (n : Nat) -> Ev n -> evn n = True
ev_thus_evn_true 0         Ev0      = Refl
ev_thus_evn_true (S (S n)) (EvSS x) = ev_thus_evn_true n x

export
evn_true_thus_ev : (n : Nat) -> evn n = True -> Ev n
evn_true_thus_ev 0         _   = Ev0
evn_true_thus_ev (S (S n)) prf = EvSS $ evn_true_thus_ev n prf

export
ev_minus : (m : Nat) -> Ev m -> Ev (m `minus` 2)
ev_minus Z         Ev0      = Ev0
ev_minus (S (S n)) (EvSS x) = rewrite minusZeroRight n in x

export
not_ev_thus_evn_false : (n : Nat) -> Not $ Ev n -> evn n = False
not_ev_thus_evn_false 0         f = absurd $ f Ev0
not_ev_thus_evn_false (S 0)     _ = Refl
not_ev_thus_evn_false (S (S k)) f = not_ev_thus_evn_false k $ f . EvSS

export
evn_false_thus_not_ev : (n : Nat) -> evn n = False -> Not $ Ev n
evn_false_thus_not_ev (S (S k)) prf (EvSS x) = evn_false_thus_not_ev k prf x

-- Example from section 3.5.2

public export
data Star : (a -> a -> Type) -> a -> a -> Type where
  Refl : Star r x x
  Step : {0 r : a -> a -> Type} -> r x y -> Star r y z -> Star r x z

export
star_trans : Star r x y -> Star r y z -> Star r x z
star_trans Refl       y = y
star_trans (Step x w) y = Step x (star_trans w y)

-- Exercise 3.2

public export
data Palindrome : List a -> Type where
  Nil  : Palindrome []
  (::) : (x : a) -> Palindrome xs -> Palindrome $ x :: xs ++ [x]

export
rev_of_palindrome : (xs : List a) -> Palindrome xs -> reverse xs = xs
rev_of_palindrome []               []     = Refl
rev_of_palindrome (x::(xs ++ [x])) (x::y) = rewrite sym $ revAppend (x::xs) [x] in
                                            rewrite sym $ revAppend [x] xs in
                                            rewrite rev_of_palindrome xs y in
                                            Refl

-- Exercise 3.3

public export
data Star' : (a -> a -> Type) -> a -> a -> Type where
  Refl' : Star' r x x
  Step' : {0 r : a -> a -> Type} -> Star' r x y -> r y z -> Star' r x z

export
star'_is_star : Star' r n m -> Star r n m
star'_is_star Refl'              = Refl
star'_is_star (Step' s'_ny r_ym) = star'_is_star s'_ny `star_trans` Step r_ym Refl

export
star'_trans : Star' r x y -> Star' r y z -> Star' r x z
star'_trans x Refl'       = x
star'_trans x (Step' y w) = Step' (star'_trans x y) w

export
star_is_star' : Star r x y -> Star' r x y
star_is_star' Refl       = Refl'
star_is_star' (Step x z) = Step' Refl' x `star'_trans` star_is_star' z

-- Execrise 3.4

public export
data Iter : (a -> a -> Type) -> Nat -> a -> a -> Type where
  IterZ : Iter r 0 x x
  IterS : {0 r : a -> a -> Type} -> r x y -> Iter r n y z -> Iter r (S n) x z

export
iter_then_star : Iter r n x y -> Star r x y
iter_then_star IterZ       = Refl
iter_then_star (IterS x z) = Step x (iter_then_star z)

export
star_then_some_iter : Star r x y -> (n ** Iter r n x y)
star_then_some_iter Refl       = (_ ** IterZ)
star_then_some_iter (Step x z) = (_ ** IterS x $ snd $ star_then_some_iter z)

-- Exercise 3.5

public export
data Alpha = A | B

namespace S
  public export
  data S : List Alpha -> Type where
    Empty : S []
    Asb   : S w -> S $ [A] ++ w ++ [B]
    Ss    : S w -> S v -> S $ w ++ v

namespace T
  public export
  data T : List Alpha -> Type where
    Empty : T []
    Tatb  : T w -> T v -> T $ w ++ [A] ++ v ++ [B]

export
s_to_t : T w -> S w
s_to_t Empty      = Empty
s_to_t (Tatb x y) = Ss (s_to_t x) $ Asb $ s_to_t y

export
t_conj : T w -> T v -> T (w ++ v)
t_conj x Empty = rewrite appendNilRightNeutral w in x
t_conj x (Tatb {v=a} {w=b} y z) = rewrite appendAssociative w b ([A] ++ a ++ [B]) in Tatb (t_conj x y) z

export
t_to_s : S w -> T w
t_to_s Empty    = Empty
t_to_s (Asb x)  = Tatb Empty $ t_to_s x
t_to_s (Ss x y) = t_conj (t_to_s x) (t_to_s y)
