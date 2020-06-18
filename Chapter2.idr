module Chapter2

import Data.List
import Data.Nat

%default total

-- Exercise 2.2

export
add_assoc : (n, m, k : Nat) -> n + (m + k) = (n + m) + k
add_assoc Z     m k = Refl
add_assoc (S n) m k = rewrite add_assoc n m k in Refl

add_z_right : (n : Nat) -> n + 0 = n
add_z_right Z     = Refl
add_z_right (S n) = rewrite add_z_right n in Refl

add_s_right : (n, m : Nat) -> n + S m = S (n + m)
add_s_right Z     m = Refl
add_s_right (S n) m = rewrite add_s_right n m in Refl

export
add_comm : (n, m : Nat) -> n + m = m + n
add_comm Z     m = rewrite add_z_right m in Refl
add_comm (S n) m = rewrite add_comm n m in
                   rewrite add_s_right m n in
                   Refl

public export
double : Nat -> Nat
double Z     = Z
double (S n) = S . S $ double n

export
double_is_add : (m : Nat) -> double m = m + m
double_is_add Z     = Refl
double_is_add (S m) = rewrite double_is_add m in
                      rewrite add_s_right m m in
                      Refl

-- Exercise 2.3

public export
count : Eq a => a -> List a -> Nat
count _ []      = 0
count x (y::xs) = if x == y
                    then S $ count x xs
                    else count x xs

export
count_le_length : Eq a => (x : a) -> (xs : List a) -> count x xs `LTE` length xs
count_le_length x []      = LTEZero
count_le_length x (y::xs) with (x == y)
  count_le_length x (_::xs) | True  = LTESucc $ count_le_length x xs
  count_le_length x (_::xs) | False = lteSuccRight $ count_le_length x xs

-- Exercise 2.4

public export
snoc : List a -> a -> List a
snoc [] n      = [n]
snoc (x::xs) n = x :: Chapter2.snoc xs n

public export
reverse : List a -> List a
reverse []      = []
reverse (x::xs) = Chapter2.snoc (Chapter2.reverse xs) x

reverse_of_snoc : (xs : List a) -> (x : a) -> Chapter2.reverse (Chapter2.snoc xs x) = x :: Chapter2.reverse xs
reverse_of_snoc [] _      = Refl
reverse_of_snoc (_::xs) n = rewrite reverse_of_snoc xs n in Refl

export
double_reverse : (xs : List a) -> Chapter2.reverse (Chapter2.reverse xs) = xs
double_reverse []      = Refl
double_reverse (x::xs) = rewrite reverse_of_snoc (Chapter2.reverse xs) x in
                         rewrite double_reverse xs in
                         Refl

-- Exercise 2.5

public export
sum_upto : Nat -> Nat
sum_upto Z     = Z
sum_upto (S n) = S n + sum_upto n

export
half : Nat -> Nat
half Z         = Z
half (S Z)     = Z
half (S (S n)) = S (half n)

half_of_add : (a : Nat) -> (n : Nat) -> a + half n = half (a + (a + n))
half_of_add Z     n = Refl
half_of_add (S k) n = rewrite sym $ plusSuccRightSucc k (k + n) in
                      rewrite half_of_add k n in
                      Refl

-- Contents of standard `Nat`'s `div` are not enclosed (somewhy), that's why I defined my own recusrive `half`.
public export
sum_upto_formula : (n : Nat) -> sum_upto n = half (n * (n + 1))
sum_upto_formula Z     = Refl
sum_upto_formula (S k) = rewrite sum_upto_formula k in
                         rewrite plusCommutative k 1 in
                         rewrite multRightSuccPlus k (S k) in
                         rewrite half_of_add k (k * S k) in
                         Refl

-- Exercise 2.6

public export
data Tree a = Tip
            | Node (Tree a) a (Tree a)

public export
contents : Tree a -> List a
contents Tip          = []
contents (Node l x r) = x :: contents l ++ contents r

public export
sum_tree : Tree Nat -> Nat
sum_tree Tip          = 0
sum_tree (Node l x r) = x + sum_tree l + sum_tree r

-- We could do this for `Num a => ... List a` asap `Num` would contain the monoid rules (zero elimintation, etc.)
sum_of_concat : (xs, ys : List Nat) -> sum (xs ++ ys) = sum xs + sum ys
sum_of_concat [] ys = rewrite plusZeroLeftNeutral (sum ys) in Refl
sum_of_concat (x::xs) ys = rewrite sum_of_concat xs ys in
                           rewrite plusAssociative x (sum xs) (sum ys) in
                           Refl

export
sum_tree_thru_contents : (tr : Tree Nat) -> sum_tree tr = sum (contents tr)
sum_tree_thru_contents Tip          = Refl
sum_tree_thru_contents (Node l x r) = rewrite sum_tree_thru_contents l in
                                      rewrite sum_tree_thru_contents r in
                                      rewrite sum_of_concat (contents l) (contents r) in
                                      rewrite plusAssociative x (sum $ contents l) (sum $ contents r) in
                                      Refl

-- Exercise 2.7

namespace Ex_2_7

  public export
  data Tree2 a = Tip
               | Leaf a
               | Node (Tree2 a) a (Tree2 a)

public export
mirror : Tree2 a -> Tree2 a
mirror n@Tip        = n
mirror n@(Leaf _)   = n
mirror (Node l x r) = Node (mirror r) x (mirror l)

mirror_of_mirror : (t : Tree2 a) -> mirror (mirror t) = t
mirror_of_mirror Tip          = Refl
mirror_of_mirror (Leaf _)     = Refl
mirror_of_mirror (Node l _ r) = rewrite mirror_of_mirror l in
                                rewrite mirror_of_mirror r in
                                Refl

public export
pre_order : Tree2 a -> List a
pre_order Tip          = []
pre_order (Leaf x)     = [x]
pre_order (Node l x r) = x :: pre_order l ++ pre_order r

public export
post_order : Tree2 a -> List a
post_order Tip          = []
post_order (Leaf x)     = [x]
post_order (Node l x r) = post_order l ++ post_order r ++ [x]

export
pre_n_post_orders : (t : Tree2 a) -> pre_order (mirror t) = Data.List.reverse (post_order t)
pre_n_post_orders Tip          = Refl
pre_n_post_orders (Leaf _)     = Refl
pre_n_post_orders (Node l x r) = rewrite pre_n_post_orders l in
                                 rewrite pre_n_post_orders r in
                                 rewrite sym $ revAppend (post_order l) (post_order r ++ [x]) in
                                 rewrite sym $ revAppend (post_order r) [x] in
                                 Refl

-- Exercise 2.8

public export
intersperse : a -> List a -> List a
intersperse _ []            = []
intersperse _ [x]           = [x]
intersperse s (x::r@(_::_)) = x :: s :: Chapter2.intersperse s r
-- The line above can be written simpler, as `intersperse s (x::y::ys) = x :: s :: Chapter2.intersperse s (y::ys)`
--   but actual definitely does not rebuild the `r`, but simpler one may rebuild this in runtime (thus, less may be effective).


export
intersperse_n_map : (s : a) -> (xs : List a) -> (f : a -> a) -> map f (Chapter2.intersperse s xs) = Chapter2.intersperse (f s) (map f xs)
intersperse_n_map s []            f = Refl
intersperse_n_map s [x]           f = Refl
intersperse_n_map s (x::r@(_::_)) f = rewrite intersperse_n_map s r f in Refl

-- Exercise 2.9

public export
itadd : Nat -> Nat -> Nat
itadd Z     m = m
itadd (S n) m = itadd n (S m)

export
itadd_is_add : (n, m : Nat) -> itadd n m = n + m
itadd_is_add Z     m = Refl
itadd_is_add (S n) m = rewrite itadd_is_add n (S m) in
                       rewrite plusSuccRightSucc n m in
                       Refl

-- Exercise 2.10

namespace Ex_2_10

  public export
  data Tree0 = Tip | Node Tree0 Tree0

public export
nodes : Tree0 -> Nat
nodes Tip        = 1
nodes (Node l r) = nodes l + nodes r + 1

public export
explode : Nat -> Tree0 -> Tree0
explode Z     t = t
explode (S n) t = explode n $ Node t t

export
explode_in_nodes : (n : Nat) -> (t : Tree0) -> nodes (explode n t) = ((2 `power` n) * nodes t + (2 `power` n)) `minus` 1
explode_in_nodes Z t = rewrite plusZeroRightNeutral $ nodes t in
                       rewrite plusCommutative (nodes t) 1 in
                       rewrite minusZeroRight $ nodes t in
                       Refl
explode_in_nodes (S n) t = rewrite explode_in_nodes n (Node t t) in
                           rewrite plusZeroRightNeutral $ 2 `power` n in
                           rewrite plusCommutative (nodes t + nodes t) 1 in
                           rewrite multRightSuccPlus (power 2 n) (nodes t + nodes t) in
                           rewrite plusCommutative (power 2 n) $ power 2 n * (nodes t + nodes t) in
                           rewrite sym $ plusAssociative (power 2 n * (nodes t + nodes t)) (power 2 n) (power 2 n) in
                           rewrite multDistributesOverPlusRight (power 2 n) (nodes t) (nodes t) in
                           rewrite multDistributesOverPlusLeft (power 2 n) (power 2 n) (nodes t) in
                           Refl

-- Exercise 2.11

-- Original `Int` was replaces with `Int` because where are not enough rules for `Int`s.

public export
data Exp = Var
         | Const Nat
         | Add Exp Exp
         | Mult Exp Exp

public export
eval : Exp -> Nat -> Nat
eval Var        x = x
eval (Const n)  _ = n
eval (Add l r)  x = eval l x + eval r x
eval (Mult l r) x = eval l x * eval r x

public export
evalp : Num a => List a -> a -> a
evalp []      _ = 0
evalp (p::ps) x = p + x * evalp ps x

infixr 8 +|+
public export
(+|+) : Num a => List a -> List a -> List a
[]      +|+ r       = r
l       +|+ []      = l
(l::ls) +|+ (r::rs) = l+r :: ls +|+ rs

export
evalp_add_lin : (l, r : List Nat) -> (x : Nat) -> evalp (l +|+ r) x = evalp l x + evalp r x
evalp_add_lin [] r x = Refl
evalp_add_lin l@(_::_) [] x = rewrite plusZeroRightNeutral (evalp l x) in Refl
evalp_add_lin (l::ls) (r::rs) x = rewrite evalp_add_lin ls rs x in
                                  rewrite multDistributesOverPlusRight x (evalp ls x) (evalp rs x) in
                                  rewrite replus l r (mult x (evalp ls x)) (mult x (evalp rs x)) in
                                  Refl
  where
    replus : (l, r, p, q : Nat) -> (l + r) + (p + q) = (l + p) + (r + q)
    replus l r p q = rewrite sym $ plusAssociative l r (p + q) in
                     rewrite plusCommutative p q in
                     rewrite plusAssociative r q p in
                     rewrite plusCommutative (r + q) p in
                     rewrite plusAssociative l p (r + q) in
                     Refl

infixr 9 *|*
public export
(*|*) : Num a => List a -> List a -> List a
[]      *|* _       = []
_       *|* []      = []
(l::ls) *|* (r::rs) = l*r :: (0 :: ls *|* rs) +|+ map (*l) rs +|+ map (*r) ls

evalp_map : (n : Nat) -> (ns : List Nat) -> (x : Nat) -> evalp (map (*n) ns) x = n * evalp ns x
evalp_map n [] x = rewrite multZeroRightZero n in Refl
evalp_map n (m::ms) x = rewrite evalp_map n ms x in
                        rewrite multAssociative x n (evalp ms x) in
                        rewrite multCommutative x n in
                        rewrite multCommutative m n in
                        rewrite multDistributesOverPlusRight n m (x * evalp ms x) in
                        rewrite multAssociative n x (evalp ms x) in
                        Refl

export
evalp_mul_lin : (l, r : List Nat) -> (x : Nat) -> evalp (l *|* r) x = evalp l x * evalp r x
evalp_mul_lin [] r x = Refl
evalp_mul_lin l@(_::_) [] x = rewrite multZeroRightZero (evalp l x) in Refl
evalp_mul_lin (l::ls) (r::rs) x = rewrite evalp_add_lin (0 :: ls *|* rs) (map (*l) rs +|+ map (*r) ls) x in
                                  rewrite evalp_add_lin (map (*l) rs) (map (*r) ls) x in
                                  rewrite evalp_mul_lin ls rs x in
                                  rewrite evalp_map r ls x in
                                  rewrite evalp_map l rs x in
                                  rewrite remult l r (evalp ls x) (evalp rs x) x in
                                  Refl
  where
    remult : (l, r, el, er, x : Nat) -> (l + x*el) * (r + x*er) = l*r + x*(x*(el*er) + (l*er + r*el))
    remult l r el er x =                                                                           -- (l + x*el) * (r + x*er)
                         rewrite multDistributesOverPlusLeft l (x*el) (r + x*er) in                -- l * (r + x*er) + (x*el)*(r + x*er)
                         rewrite multDistributesOverPlusRight l r (x*er) in                        -- (l*r + l*(x*er)) + (x*el)*(r + x*er)
                         rewrite multDistributesOverPlusRight (x*el) r (x*er) in                   -- (l*r + l*(x*er)) + ((x*el)*r + (x*el)*(x*er))
                         rewrite multAssociative l x er in                                         -- (l*r + (l*x)*er) + ((x*el)*r + (x*el)*(x*er))
                         rewrite multCommutative l x in                                            -- (l*r + (x*l)*er) + ((x*el)*r + (x*el)*(x*er))
                         rewrite sym $ multAssociative x l er in                                   -- (l*r + x*(l*er)) + ((x*el)*r + (x*el)*(x*er))
                         rewrite sym $ multAssociative x el r in                                   -- (l*r + x*(l*er)) + (x*(el*r) + (x*el)*(x*er))
                         rewrite sym $ multAssociative x el (x*er) in                              -- (l*r + x*(l*er)) + (x*(el*r) + x*(el*(x*er)))
                         rewrite multAssociative el x er in                                        -- (l*r + x*(l*er)) + (x*(el*r) + x*((el*x)*er))
                         rewrite multCommutative el x in                                           -- (l*r + x*(l*er)) + (x*(el*r) + x*((x*el)*er))
                         rewrite sym $ multAssociative x el er in                                  -- (l*r + x*(l*er)) + (x*(el*r) + x*(x*(el*er)))
                         rewrite multCommutative el r in                                           -- (l*r + x*(l*er)) + (x*(r*el) + x*(x*(el*er)))
                         rewrite sym $ multDistributesOverPlusRight x (r*el) (x*(el*er)) in        -- (l*r + x*(l*er)) + x*(r*el + x*(el*er))
                         rewrite plusCommutative (r*el) (x*(el*er)) in                             -- (l*r + x*(l*er)) + x*(x*(el*er) + r*el)
                         rewrite sym $ plusAssociative (l*r) (x*(l*er)) (x*(x*(el*er) + r*el)) in  -- l*r + (x*(l*er) + x*(x*(el*er) + r*el))
                         rewrite sym $ multDistributesOverPlusRight x (l*er) (x*(el*er) + r*el) in -- l*r + x*(l*er + (x*(el*er) + r*el))
                         rewrite plusAssociative (l*er) (x*(el*er)) (r*el) in                      -- l*r + x*((l*er + x*(el*er)) + r*el)
                         rewrite plusCommutative (l*er) (x*(el*er)) in                             -- l*r + x*((x*(el*er) + l*er) + r*el)
                         rewrite sym $ plusAssociative (x*(el*er)) (l*er) (r*el) in                -- l*r + x*(x*(el*er) + (l*er + r*el))
                         Refl

public export
coeffs : Exp -> List Nat
coeffs Var        = [0, 1]
coeffs (Const n)  = [n]
coeffs (Add l r)  = coeffs l +|+ coeffs r
coeffs (Mult l r) = coeffs l *|* coeffs r

export
evalp_of_coeffs_is_eval : (e : Exp) -> (x : Nat) -> evalp (coeffs e) x = eval e x
evalp_of_coeffs_is_eval Var x = rewrite multZeroRightZero x in
                                rewrite multOneRightNeutral x in
                                Refl
evalp_of_coeffs_is_eval (Const n) x = rewrite multZeroRightZero x in
                                      rewrite plusZeroRightNeutral n in
                                      Refl
evalp_of_coeffs_is_eval (Add l r) x = rewrite evalp_add_lin (coeffs l) (coeffs r) x in
                                      rewrite evalp_of_coeffs_is_eval l x in
                                      rewrite evalp_of_coeffs_is_eval r x in
                                      Refl
evalp_of_coeffs_is_eval (Mult l r) x = rewrite evalp_mul_lin (coeffs l) (coeffs r) x in
                                       rewrite evalp_of_coeffs_is_eval l x in
                                       rewrite evalp_of_coeffs_is_eval r x in
                                       Refl
