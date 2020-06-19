module Data.InSet

import Data.Bool
import Data.Bool.Xor
import Decidable.Equality

%default total

---------------------
---------------------
---               ---
---  DEFINITIONS  ---
---               ---
---------------------
---------------------

infix 6 ==
infix 7 `isin`, `notin`
infixl 8 +, -, ^
infixl 9 *, #

-------------------
--- Type itself ---
-------------------

public export
InSet : Type -> Type
InSet a = a -> Bool

------------------------------------
--- Intesional test of existence ---
------------------------------------

export
isin : a -> InSet a -> Bool
isin = flip apply

public export %inline
notin : a -> InSet a -> Bool
notin x y = not $ isin x y

----------------
--- Creation ---
----------------

--- Syntax for list-like literals ---

public export
Nil : InSet a
Nil _ = False

public export
(::) : Eq a => a -> InSet a -> InSet a
(::) added parent x = if x == added then True else x `isin` parent

--- Constants

public export %inline
Empty : InSet a
Empty = []

public export
Universe : InSet a
Universe _ = True

---------------------------
--- Basic set relations ---
---------------------------

public export
(==) : InSet a -> InSet a -> Type
sa == sb = (x : a) -> x `isin` sa = x `isin` sb

public export
(<=) : InSet a -> InSet a -> Type
sa <= sb = (x : a) -> x `isin` sa = True -> x `isin` sb = True

public export
NotEmpty : {a : Type} -> InSet a -> Type
NotEmpty s = (x ** x `isin` s = True)

----------------------------
--- Basic set operations ---
----------------------------

export
(+) : InSet a -> InSet a -> InSet a -- union
(+) sa sb x = x `isin` sa || x `isin` sb

export
(#) : InSet a -> InSet a -> InSet a -- intersection
(#) sa sb x = x `isin` sa && x `isin` sb

export
(-) : InSet a -> InSet a -> InSet a -- set difference
(-) sa sb x = x `isin` sa && x `notin` sb

export
(^) : InSet a -> InSet a -> InSet a -- symmetrical difference
(^) sa sb x = (x `isin` sa) `xor` (x `isin` sb)

export %inline
complement : InSet a -> InSet a
complement s x = x `notin` s

------------------------------------
--- Non-algebraic set operations ---
------------------------------------

export
(*) : InSet a -> InSet b -> InSet (a, b)
(*) sx sy (x, y) = x `isin` sx && y `isin` sy

--------------
--------------
---        ---
---  LAWS  ---
---        ---
--------------
--------------

------------------------
--- Laws of equality ---
------------------------

export
eq_reflexivity : (0 s : InSet a) -> s == s
eq_reflexivity _ _ = Refl

export
eq_symmerty : {0 sa, sb : InSet a} -> (0 _ : sa == sb) -> sb == sa
eq_symmerty f x = rewrite f x in Refl

export
eq_transitivity : {0 sa, sb, sc : InSet a} -> (0 _ : sa == sb) -> (0 _ : sb == sc) -> sa == sc
eq_transitivity f g x = rewrite f x in
                        rewrite g x in
                        Refl

-- Definition above can be written as
--   sa <= sb = (x : a) -> So (x `isin` sa) -> So (x `isin` sb)
-- but this leads to constant using `soToEq` and `eqToSo` in proofs.

--- Negative equality-related laws ---

trueNotFalse : Not (True = False)
trueNotFalse Refl impossible

export
non_empty_is_not_empty : NotEmpty s -> Not (s = Empty)
non_empty_is_not_empty (x ** prf_t) prf_f = trueNotFalse $ rewrite sym prf_t in rewrite prf_f in Refl

export
non_empty_not_eq_empty : NotEmpty s -> Not (s == Empty)
non_empty_not_eq_empty (x ** prf_t) prf_f = trueNotFalse $ rewrite sym prf_t in rewrite prf_f x in Refl

export
cant_in_and_not_in : (s : InSet a) -> (x : a) -> Not (x `isin` s = x `notin` s)
cant_in_and_not_in s x prf with (s x)
  cant_in_and_not_in _ _ Refl | True impossible

--- Connection with external equality ---

export
eq_appended_eq : Eq a => (s : InSet a) -> {0 n, m : a} -> n == m = True -> [n] + s == [m] + s
-- can be implemented only when `(x == n) /\ (x == m) ==> (n == m)`

export
x_in_x_etc : Eq a => (0 s : InSet a) -> (0 x : a) -> (0 eq_refl : x == x = True) -> x `isin` (x::s) = True
x_in_x_etc _ _ eq_refl = rewrite eq_refl in Refl

-------------------------------
--- Laws of subset relation ---
-------------------------------

--- Order laws of subset relation ---

export
subset_equal : {0 sa, sb : InSet a} -> (0 _ : sa == sb) -> sa <= sb
subset_equal f x prf = rewrite sym $ f x in
                       rewrite prf in
                       Refl

export
subset_reflexivity : (0 s : InSet a) -> s <= s
subset_reflexivity _ _ = id

export
subset_antisymmetry : {sa, sb : InSet a} -> sa <= sb -> sb <= sa -> sa == sb
subset_antisymmetry f g x with (decEq (sa x) True)
  subset_antisymmetry f _ x | Yes pa with (decEq (sb x) True)
    subset_antisymmetry _ _ _ | Yes pa | Yes pb = rewrite pa in
                                                  rewrite pb in
                                                  Refl
    subset_antisymmetry f _ x | Yes pa | No nb = absurd . nb $ f x pa
  subset_antisymmetry _ g x | No pa with (decEq (sb x) True)
    subset_antisymmetry _ _ _ | No na | No nb = rewrite notTrueIsFalse na in
                                                rewrite notTrueIsFalse nb in
                                                Refl
    subset_antisymmetry _ g x | No na | Yes pb = absurd . na $ g x pb

export
subset_transitivity : {0 sa, sb, sc : InSet a} -> (0 _ : sa <= sb) -> (0 _ : sb <= sc) -> sa <= sc
subset_transitivity f g x y = rewrite g x (f x y) in Refl

-- Subset relation's totality seems to be unprovable for intensional sets neither in
--   `Either (sa <= sb) (sb <= sa)`, nor in `Not $ sa <= sb => sb <= sa` variant.

--- Alternative subset representations with unions and intersections ---

export
subset_thru_union : {sa, sb : InSet a} -> (0 _ : sa <= sb) -> sa + sb == sb
subset_thru_union f x with (decEq (sa x) True)
  subset_thru_union f x | Yes pa = rewrite pa in
                                   rewrite f x pa in
                                   Refl
  subset_thru_union _ _ | No na = rewrite notTrueIsFalse na in Refl

export
union_thru_subset : {0 sa, sb : InSet a} -> (0 _ : sa + sb == sb) -> sa <= sb
union_thru_subset f x y = rewrite sym $ f x in
                          rewrite y in
                          Refl

export
subset_thru_intersection : {sa, sb : InSet a} -> (0 _ : sa <= sb) -> sa # sb == sa
subset_thru_intersection f x with (decEq (sa x) True)
  subset_thru_intersection f x | Yes pa = rewrite pa in
                                          rewrite f x pa in
                                          Refl
  subset_thru_intersection _ _ | No na = rewrite notTrueIsFalse na in Refl

export
intersection_thru_subset : {0 sa, sb : InSet a} -> (0 _ : sa # sb == sa) -> sa <= sb
intersection_thru_subset f x pa = rewrite sym pa in
                                  rewrite sym $ f x in
                                  rewrite pa in
                                  Refl

--- Subset with binary set operations ---

export
subset_for_unioned_right : {0 sa, sb : InSet a} -> (0 sc : InSet a) -> (0 _ : sa <= sb) -> sa <= sb + sc
subset_for_unioned_right sc f x prf = rewrite f x prf in Refl

and_true_left_true : (a, b : Bool) -> a && b = True -> a = True
and_true_left_true True _ _ = Refl

export
subset_for_intersected_left : {0 sa, sb : InSet a} -> (0 sc : InSet a) -> (0 _ : sa <= sb) -> (sa # sc) <= sb
subset_for_intersected_left sc f x prf = rewrite f x $ and_true_left_true (sa x) (sc x) prf in Refl

export
subset_for_diffed_left : {0 sa, sb : InSet a} -> (0 sc : InSet a) -> (0 _ : sa <= sb) -> (sa - sc) <= sb
subset_for_diffed_left sc f x prf = rewrite f x $ and_true_left_true (sa x) (x `notin` sc) prf in Refl

-- Particular cases for the properties from above, where `sb = sa`

export
subset_refl_unioned_right : (0 sa, sc : InSet a) -> sa <= sa + sc
subset_refl_unioned_right sa sc = subset_for_unioned_right sc $ subset_reflexivity sa

export
subset_refl_intersected_left : (0 sa, sc : InSet a) -> (sa # sc) <= sa
subset_refl_intersected_left sa sc = subset_for_intersected_left sc $ subset_reflexivity sa

export
subset_refl_diffed_left : (0 sa, sc : InSet a) -> (sa - sc) <= sa
subset_refl_diffed_left sa sc = subset_for_diffed_left sc $ subset_reflexivity sa

--- Subset with complement ---

export
subset_of_complements : {0 sa, sb : InSet a} -> (0 _ : sa <= sb) -> complement sb <= complement sa
subset_of_complements f x prf = rewrite sym $ subset_thru_intersection f x in
                                rewrite the (sb x = False) $ rewrite sym $ notInvolutive $ sb x in cong not prf in
                                rewrite andFalseFalse $ sa x in
                                Refl

export
subset_of_complements_back : {0 sa, sb : InSet a} -> (0 _ : complement sb <= complement sa) -> sa <= sb
subset_of_complements_back f x prf = rewrite sym $ subset_of_complements f x (rewrite notInvolutive $ sa x in prf) in
                                     rewrite notInvolutive $ sb x in
                                     Refl

--------------------------------------------------
--- Congruence of relations in specializations ---
--------------------------------------------------

--- Append ---

export
append_eq_cong : Eq a => {0 sa, sb : InSet a} -> (n : a) -> (0 _ : sa == sb) -> n::sa == n::sb
append_eq_cong n f x with (x == n)
  append_eq_cong _ _ _ | True  = Refl
  append_eq_cong _ f x | False = rewrite f x in Refl

--- Union ---

export
union_eq_cong_l : {0 sa, sb : InSet a} -> (0 sc : InSet a) -> (0 _ : sa == sb) -> sa + sc == sb + sc
union_eq_cong_l _ f x = rewrite f x in Refl

export
union_eq_cong_r : {0 sa, sb : InSet a} -> (0 sc : InSet a) -> (0 _ : sa == sb) -> sc + sa == sc + sb
union_eq_cong_r _ f x = rewrite f x in Refl

-- TODO to add for subset

--- Intersection ---

-- TODO to add for equality

-- TODO to add for subset

--- Difference ---

-- TODO to add for equality

-- TODO to add for subset

--- Symmetrical difference ---

-- TODO to add for equality

-- TODO to add for subset

--- Complement ---

-- TODO to add for equality

-- TODO to add for subset

--- Cartesian product ---

export
cart_eq_cong_l : {0 sa, sb : InSet a} -> (0 sc : InSet c) -> (0 _ : sa == sb) -> sc * sa == sc * sb

export
cart_eq_cong_r : {0 sa, sb : InSet a} -> (0 sc : InSet c) -> (0 _ : sa == sb) -> sa * sc == sb * sc

export
cart_subset_cong_l : {0 sa, sb : InSet a} -> (0 sc : InSet c) -> (0 _ : sa <= sb) -> sc * sa <= sc * sb

export
cart_subset_cong_r : {0 sa, sb : InSet a} -> (0 sc : InSet c) -> (0 _ : sa <= sb) -> sa * sc <= sb * sc

----------------------
--- Laws of append ---
----------------------

export
append_is_union : Eq a => (n : a) -> (0 s : InSet a) -> n::s == [n] + s
append_is_union n _ x with (x == n)
  append_is_union _ _ _ | True  = Refl
  append_is_union _ _ _ | False = Refl

---------------------
--- Laws of union ---
---------------------

export
union_of_self : (0 s : InSet a) -> s + s == s
union_of_self s x = rewrite orSameNeutral $ s x in Refl

export
union_commutative : (0 sa, sb : InSet a) -> sa + sb == sb + sa
union_commutative sa sb x = rewrite orCommutative (sa x) (sb x) in Refl

export
union_associative : (0 sa, sb, sc : InSet a) -> sa + (sb + sc) == (sa + sb) + sc
union_associative sa sb sc x = rewrite orAssociative (sa x) (sb x) (sc x) in Refl

export
union_empty_neutral : (0 s : InSet a) -> s + [] == s
union_empty_neutral s x = rewrite orFalseNeutral $ s x in Refl

export
union_preserves_universe : (0 s : InSet a) -> s + Universe == Universe
union_preserves_universe s x = rewrite orTrueTrue $ s x in Refl

-- ... with intersection

export
union_distributes_over_intersection : (0 sa, sb, sc : InSet a) -> sa + (sb # sc) == (sa + sb) # (sa + sc)
union_distributes_over_intersection sa sb sc x = rewrite orDistribAndR (sa x) (sb x) (sc x) in Refl

-- ... with diff

export
union_with_diff : (0 sa, sb, sc : InSet a) -> sa + (sb - sc) == (sa + sb) - (sc - sa)
union_with_diff sa sb sc x = rewrite orDistribAndR (sa x) (sb x) (not $ sc x) in
                             rewrite notAndIsOr (sc x) (not $ sa x) in
                             rewrite notInvolutive $ sa x in
                             rewrite orCommutative (sa x) (not $ sc x) in
                             Refl

-- ... with symdiff

-- TODO To make this functon to have `(0 sa, sb : InSet a)` in the signature.
export
union_thru_symdiff_and_intersection : (sa, sb : InSet a) -> sa + sb == (sa ^ sb) ^ (sa # sb)
union_thru_symdiff_and_intersection sa sb x = case (decEq (sa x) True, decEq (sb x) True) of
  (Yes pa, Yes pb) => rewrite pa in                 rewrite pb in                 Refl
  (Yes pa, No  nb) => rewrite pa in                 rewrite notTrueIsFalse nb in  Refl
  (No  na, Yes pb) => rewrite notTrueIsFalse na in  rewrite pb in                 Refl
  (No  na, No  nb) => rewrite notTrueIsFalse na in  rewrite notTrueIsFalse nb in  Refl

-- ... with complement

export
union_with_its_complement : (0 s : InSet a) -> s + complement s == Universe
union_with_its_complement s x = rewrite orNotTrue $ s x in Refl

----------------------------
--- Laws of intersection ---
----------------------------

export
intersection_of_self : (0 s : InSet a) -> s # s == s
intersection_of_self s x = rewrite andSameNeutral $ s x in Refl

export
intersection_commutative : (0 sa, sb : InSet a) -> sa # sb == sb # sa
intersection_commutative sa sb x = rewrite andCommutative (sa x) (sb x) in Refl

export
intersection_associative : (0 sa, sb, sc : InSet a) -> sa # (sb # sc) == (sa # sb) # sc
intersection_associative sa sb sc x = rewrite andAssociative (sa x) (sb x) (sc x) in Refl

export
intersection_universe_neutral : (0 s : InSet a) -> s # Universe == s
intersection_universe_neutral s x = rewrite andTrueNeutral $ s x in Refl

export
intersection_preserves_empty : (0 s : InSet a) -> s # [] == []
intersection_preserves_empty s x = rewrite andFalseFalse $ s x in Refl

-- ... with union

export
intersection_distributes_over_union : (0 sa, sb, sc : InSet a) -> sa # (sb + sc) == (sa # sb) + (sa # sc)
intersection_distributes_over_union sa sb sc x = rewrite andDistribOrR (sa x) (sb x) (sc x) in Refl

-- ... with set diff

export
intersection_diff_swap : (0 sa, sb, sc : InSet a) -> sa # (sb - sc) == sb # (sa - sc)
intersection_diff_swap sa sb sc x = rewrite andAssociative (sa x) (sb x) (not $ sc x) in
                                    rewrite andAssociative (sb x) (sa x) (not $ sc x) in
                                    rewrite andCommutative (sa x) (sb x) in
                                    Refl

export
intersection_diff_assoc : (0 sa, sb, sc : InSet a) -> sa # (sb - sc) == (sa # sb) - sc
intersection_diff_assoc sa sb sc x = rewrite sym $ andAssociative (sa x) (sb x) (not $ sc x) in Refl

-- ... with symmetrical diff

-- TODO To make this functon to have `(0 sa, sb, sc : InSet a)` in the signature.
export
intersection_distributes_over_symdiff : (sa, sb, sc : InSet a) -> sa # (sb ^ sc) == (sa # sb) ^ (sa # sc)
intersection_distributes_over_symdiff sa sb sc x = case decEq (sa x) True of
  Yes pa => rewrite pa in Refl
  No na => rewrite notTrueIsFalse na in Refl

-- ... with complement

export
intersection_with_complement : (0 sa, sb : InSet a) -> sa # complement sb == sa - sb
intersection_with_complement _ _ _ = Refl

export
intersection_with_its_complement : (0 s : InSet a) -> s # complement s == []
intersection_with_its_complement s x = rewrite andNotFalse $ s x in Refl

------------------------------
--- Laws of set difference ---
------------------------------

export
diff_of_intersection : (0 sa, sb, sc : InSet a) -> sc - (sa # sb) == (sc - sa) + (sc - sb)
diff_of_intersection sa sb sc x = rewrite notAndIsOr (sa x) (sb x) in
                                  rewrite andDistribOrR (sc x) (not $ sa x) (not $ sb x) in
                                  Refl

export
diff_of_union : (0 sa, sb, sc : InSet a) -> sc - (sa + sb) == (sc - sa) # (sc - sb)
diff_of_union sa sb sc x = rewrite notOrIsAnd (sa x) (sb x) in
                           rewrite andAssociative (sc x && not (sa x)) (sc x) (not $ sb x) in
                           rewrite sym $ andAssociative (sc x) (not $ sa x) (sc x) in
                           rewrite andCommutative (not $ sa x) (sc x) in
                           rewrite andAssociative (sc x) (sc x) (not $ sa x) in
                           rewrite andSameNeutral $ sc x in
                           rewrite andAssociative (sc x) (not $ sa x) (not $ sb x) in
                           Refl

export
diff_of_diff : (0 sa, sb, sc : InSet a) -> sc - (sb - sa) == (sc # sa) + (sc - sb)
diff_of_diff sa sb sc x = rewrite notAndIsOr (sb x) (not $ sa x) in
                          rewrite notInvolutive $ sa x in
                          rewrite orCommutative (not $ sb x) (sa x) in
                          rewrite andDistribOrR (sc x) (sa x) (not $ sb x) in
                          Refl

export
diff_of_self : (0 s : InSet a) -> s - s == []
diff_of_self s x = rewrite andNotFalse $ s x in Refl

export
diff_of_empty_left : (0 s : InSet a) -> [] - s == []
diff_of_empty_left _ _ = Refl

export
diff_of_empty_right : (0 s : InSet a) -> s - [] == s
diff_of_empty_right s x = rewrite andTrueNeutral $ s x in Refl

export
diff_of_universe : (0 s : InSet a) -> s - Universe == []
diff_of_universe s x = rewrite andFalseFalse $ s x in Refl

export
diff_of_complements : (0 sa, sb : InSet a) -> complement sa - complement sb == sb - sa
diff_of_complements sa sb x = rewrite andCommutative (sb x) (not $ sa x) in
                              rewrite notInvolutive $ sb x in
                              Refl

--------------------------------------
--- Laws of symmetrical difference ---
--------------------------------------

-- TODO To make this functon to have `(0 sa, sb : InSet a)` in the signature.
export
symdiff_as_union_of_diffs : (sa, sb : InSet a) -> sa ^ sb == (sa - sb) + (sb - sa)
symdiff_as_union_of_diffs sa sb x = case (decEq (sa x) True, decEq (sb x) True) of
  (Yes pa, Yes pb) => rewrite pa in                 rewrite pb in                 Refl
  (Yes pa, No  nb) => rewrite pa in                 rewrite notTrueIsFalse nb in  Refl
  (No  na, Yes pb) => rewrite notTrueIsFalse na in  rewrite pb in                 Refl
  (No  na, No  nb) => rewrite notTrueIsFalse na in  rewrite notTrueIsFalse nb in  Refl

-- TODO To make this functon to have `(0 sa, sb : InSet a)` in the signature.
export
symdiff_as_diff_of_ui : (sa, sb : InSet a) -> sa ^ sb == (sa + sb) - (sa # sb)
symdiff_as_diff_of_ui sa sb x = case (decEq (sa x) True, decEq (sb x) True) of
  (Yes pa, Yes pb) => rewrite pa in                 rewrite pb in                 Refl
  (Yes pa, No  nb) => rewrite pa in                 rewrite notTrueIsFalse nb in  Refl
  (No  na, Yes pb) => rewrite notTrueIsFalse na in  rewrite pb in                 Refl
  (No  na, No  nb) => rewrite notTrueIsFalse na in  rewrite notTrueIsFalse nb in  Refl

export
symdiff_commutative : (0 sa, sb : InSet a) -> sa ^ sb == sb ^ sa
symdiff_commutative sa sb x = rewrite xorCommutative (sa x) (sb x) in Refl

export
symdiff_associative : (0 sa, sb, sc : InSet a) -> sa ^ (sb ^ sc) == (sa ^ sb) ^ sc
symdiff_associative sa sb sc x = rewrite xorAssociative (sa x) (sb x) (sc x) in Refl

export
symdiff_with_empty : (0 s : InSet a) -> s ^ [] == s
symdiff_with_empty s x = rewrite xorCommutative (s x) False in
                         rewrite xorFalseNeutral $ s x in
                         Refl

export
symdiff_with_self : (0 s : InSet a) -> s ^ s == []
symdiff_with_self s x = rewrite xorSameFalse $ s x in Refl

-- TODO To make this functon to have `(0 sa, sb, sc : InSet a)` in the signature.
export
symdiff_twice_negates : (sa, sb, sc : InSet a) -> (sa ^ sb) ^ (sb ^ sc) == sa ^ sc
symdiff_twice_negates sa sb sc x = rewrite xorCommutative (sa x) (sb x) in
                                   case decEq (sb x) True of
                                     Yes pb => rewrite pb in
                                               rewrite xorTrueNot $ sa x in
                                               rewrite xorTrueNot $ sc x in
                                               rewrite notXorCancel (sa x) (sc x) in
                                               Refl
                                     No nb => rewrite notTrueIsFalse nb in
                                              rewrite xorFalseNeutral $ sa x in
                                              rewrite xorFalseNeutral $ sc x in
                                              Refl

export
symdiff_of_complements : (0 sa, sb : InSet a) -> sa ^ sb == complement sa ^ complement sb
symdiff_of_complements sa sb x = rewrite notXorCancel (sa x) (sb x) in Refl

--------------------------
--- Laws of complement ---
--------------------------

export
comp_of_union : (0 sa, sb : InSet a) -> complement (sa + sb) == complement sa # complement sb
comp_of_union sa sb x = rewrite notOrIsAnd (sa x) (sb x) in Refl

export
comp_of_intersection : (0 sa, sb : InSet a) -> complement (sa # sb) == complement sa + complement sb
comp_of_intersection sa sb x = rewrite notAndIsOr (sa x) (sb x) in Refl

export
comp_of_empty : complement [] == Universe
comp_of_empty _ = Refl

export
comp_of_universe : complement Universe == []
comp_of_universe _ = Refl

export
comp_involutive : (0 s : InSet a) -> complement (complement s) == s
comp_involutive s x = rewrite notInvolutive $ s x in Refl

export
comp_of_diff : (0 sa, sb : InSet a) -> complement (sa - sb) == complement sa + sb
comp_of_diff sa sb x = rewrite notAndIsOr (sa x) (not $ sb x) in
                       rewrite notInvolutive $ sb x in
                       Refl

---------------------------------
--- Laws of cartesian product ---
---------------------------------

--- Operations over cartesian products at both sides:

export
intersection_of_carts : (0 sa, sb : InSet a) -> (0 sc, sd : InSet c) -> (sa * sc) # (sb * sd) == (sa # sb) * (sc # sd)

export
diff_of_carts : (0 sa, sb : InSet a) -> (0 sc, sd : InSet c) -> (sa * sc) - (sb * sd) == sa * (sc - sd) + (sa - sb) * sc

export
union_of_carts : (0 sa, sb : InSet a) -> (0 sc, sd : InSet c) -> (sa * sc) + (sb * sd) == ((sa - sb) * sc) # ((sa # sb) * (sc + sd)) # ((sb - sa) * sd)

--- Distributivity:

export
cart_distributes_over_intersection : (0 sa : InSet a) -> (0 sb, sc : InSet b) -> sa * (sb # sc) == (sa * sb) # (sa * sc)

export
cart_distributes_over_union : (0 sa : InSet a) -> (0 sb, sc : InSet b) -> sa * (sb + sc) == (sa * sb) + (sa * sc)

export
cart_distributes_over_diff : (0 sa : InSet a) -> (0 sb, sc : InSet b) -> sa * (sb - sc) == (sa * sb) - (sa * sc)

export
complement_of_cart : (0 sa : InSet a) -> (0 sb : InSet b) -> complement (sa * sb) = (complement sa * complement sb) + (complement sa * sb) + (sa * complement sb)

--- Cartesian products with relations

export
subset_of_carts_drops_l : {0 sa, sb : InSet a} -> {0 sc, sd : InSet c} -> (0 _ : NotEmpty sa) -> (0 _ : NotEmpty sc) ->
                          (0 _ : (sa * sc) <= (sb * sd)) -> sa <= sb

export
subset_of_carts_drops_r : {0 sa, sb : InSet a} -> {0 sc, sd : InSet c} -> (0 _ : NotEmpty sa) -> (0 _ : NotEmpty sc) ->
                          (0 _ : (sa * sc) <= (sb * sd)) -> sc <= sd

export
cart_of_subsets : {0 sa, sb : InSet a} -> {0 sc, sd : InSet c} -> (0 _ : sa <= sb) -> (0 _ : sc <= sd) -> (sa * sc) <= (sb * sd)
