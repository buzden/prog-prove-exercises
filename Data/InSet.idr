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

export
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

public export %inline
Empty : InSet a
Empty _ = False

export
Universe : InSet a
Universe _ = True

--- Syntax for list-like literals ---

export %inline
Nil : InSet a
Nil = Empty

export
(::) : Eq a => a -> InSet a -> InSet a
(::) added parent x = if x == added then True else x `isin` parent

---------------------------
--- Basic set relations ---
---------------------------

export
(==) : InSet a -> InSet a -> Type
sa == sb = (x : a) -> x `isin` sa = x `isin` sb

export
(<=) : InSet a -> InSet a -> Type
sa <= sb = (x : a) -> x `isin` sa = True -> x `isin` sb = True

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
eq_reflexivity : (s : InSet a) -> s == s
eq_reflexivity _ _ = Refl

export
eq_symmerty : (sa, sb : InSet a) -> sa == sb -> sb == sa
eq_symmerty _ _ f x = rewrite f x in Refl

export
eq_transitivity : (sa, sb, sc : InSet a) -> sa == sb -> sb == sc -> sa == sc
eq_transitivity _ _ _ f g x = rewrite f x in
                              rewrite g x in
                              Refl

-- Definition above can be written as
--   sa <= sb = (x : a) -> So (x `isin` sa) -> So (x `isin` sb)
-- but this leads to constant using `soToEq` and `eqToSo` in proofs.

-------------------------------
--- Laws of subset relation ---
-------------------------------

--- Order laws of subset relation ---

export
subset_reflexivity : (s : InSet a) -> s <= s
subset_reflexivity _ _ = id

export
subset_antisymmetry : (sa, sb : InSet a) -> sa <= sb -> sb <= sa -> sa == sb
subset_antisymmetry sa sb f g x with (decEq (sa x) True)
  subset_antisymmetry _ sb f _ x | Yes pa with (decEq (sb x) True)
    subset_antisymmetry _ _ _ _ _ | Yes pa | Yes pb = rewrite pa in
                                                      rewrite pb in
                                                      Refl
    subset_antisymmetry _ _ f _ x | Yes pa | No nb = absurd . nb $ f x pa
  subset_antisymmetry _ sb _ g x | No pa with (decEq (sb x) True)
    subset_antisymmetry _ _ _ _ _ | No na | No nb = rewrite notTrueIsFalse na in
                                                    rewrite notTrueIsFalse nb in
                                                    Refl
    subset_antisymmetry _ _ _ g x | No na | Yes pb = absurd . na $ g x pb

export
subset_transitivity : (sa, sb, sc : InSet a) -> sa <= sb -> sb <= sc -> sa <= sc
subset_transitivity _ _ _ f g x y = g x (f x y)

-- Subset relation's totality seems to be unprovable for intensional sets neither in
--   `Either (sa <= sb) (sb <= sa)`, nor in `Not $ sa <= sb => sb <= sa` variant.

--- Alternative subset representations with unions and intersections ---

export
subset_thru_union : (sa, sb : InSet a) -> sa <= sb -> sa + sb == sb
subset_thru_union sa _ f x with (decEq (sa x) True)
  subset_thru_union _ _ f x | Yes pa = rewrite pa in
                                       rewrite f x pa in
                                       Refl
  subset_thru_union _ _ _ _ | No na = rewrite notTrueIsFalse na in Refl

export
union_thru_subset : (sa, sb : InSet a) -> sa + sb == sb -> sa <= sb
union_thru_subset _ _ f x y = rewrite sym $ f x in
                              rewrite y in
                              Refl

export
subset_thru_intersection : (sa, sb : InSet a) -> sa <= sb -> sa # sb == sa
subset_thru_intersection sa _ f x with (decEq (sa x) True)
  subset_thru_intersection _ _ f x | Yes pa = rewrite pa in
                                              rewrite f x pa in
                                              Refl
  subset_thru_intersection _ _ _ _ | No na = rewrite notTrueIsFalse na in Refl

export
intersection_thru_subset : (sa, sb : InSet a) -> sa # sb == sa -> sa <= sb
intersection_thru_subset _ _ f x pa = rewrite sym pa in
                                      rewrite sym $ f x in
                                      rewrite pa in
                                      Refl

--- Subset with binary set operations ---

export
subset_for_unioned_right : (sa, sb, sc : InSet a) -> sa <= sb -> sa <= sb + sc
subset_for_unioned_right sa sb sc f x prf = rewrite f x prf in Refl

and_true_left_true : (a, b : Bool) -> a && b = True -> a = True
and_true_left_true True _ _ = Refl

export
subset_for_intersected_left : (sa, sb, sc : InSet a) -> sa <= sb -> (sa # sc) <= sb
subset_for_intersected_left sa sb sc f x prf = f x $ and_true_left_true (sa x) (sc x) prf
  where

export
subset_for_diffed_left : (sa, sb, sc : InSet a) -> sa <= sb -> (sa - sc) <= sb
subset_for_diffed_left sa sb sc f x prf = f x $ and_true_left_true (sa x) (x `notin` sc) prf

--- Subset with complement ---

export
subset_of_complements : (sa, sb : InSet a) -> sa <= sb -> complement sb <= complement sa
subset_of_complements sa sb f x prf = rewrite sym $ subset_thru_intersection sa sb f x in
                                      rewrite the (sb x = False) $ rewrite sym $ notInvolutive $ sb x in cong not prf in
                                      rewrite andFalseFalse $ sa x in
                                      Refl

export
subset_of_complements_back : (sa, sb : InSet a) -> complement sb <= complement sa -> sa <= sb
subset_of_complements_back sa sb f x prf = rewrite sym $ subset_of_complements (complement sb) (complement sa) f x (rewrite notInvolutive $ sa x in prf) in
                                           rewrite notInvolutive $ sb x in
                                           Refl

---------------------
--- Laws of union ---
---------------------

export
union_of_self : (s : InSet a) -> s + s == s
union_of_self s x = rewrite orSameNeutral $ s x in Refl

export
union_commutative : (sa, sb : InSet a) -> sa + sb == sb + sa
union_commutative sa sb x = rewrite orCommutative (sa x) (sb x) in Refl

export
union_associative : (sa, sb, sc : InSet a) -> sa + (sb + sc) == (sa + sb) + sc
union_associative sa sb sc x = rewrite orAssociative (sa x) (sb x) (sc x) in Refl

export
union_empty_neutral : (s : InSet a) -> s + [] == s
union_empty_neutral s x = rewrite orFalseNeutral $ s x in Refl

export
union_preserves_universe : (s : InSet a) -> s + Universe == Universe
union_preserves_universe s x = rewrite orTrueTrue $ s x in Refl

-- ... with intersection

export
union_distributes_over_intersection : (sa, sb, sc : InSet a) -> sa + (sb # sc) == (sa + sb) # (sa + sc)
union_distributes_over_intersection sa sb sc x = rewrite orDistribAndR (sa x) (sb x) (sc x) in Refl

-- ... with diff

export
union_with_diff : (sa, sb, sc : InSet a) -> sa + (sb - sc) == (sa + sb) - (sc - sa)
union_with_diff sa sb sc x = rewrite orDistribAndR (sa x) (sb x) (not $ sc x) in
                             rewrite notAndIsOr (sc x) (not $ sa x) in
                             rewrite notInvolutive $ sa x in
                             rewrite orCommutative (sa x) (not $ sc x) in
                             Refl

-- ... with symdiff

export
union_thru_symdiff_and_intersection : (sa, sb : InSet a) -> sa + sb == (sa ^ sb) ^ (sa # sb)
union_thru_symdiff_and_intersection sa sb x = case (decEq (sa x) True, decEq (sb x) True) of
  (Yes pa, Yes pb) => rewrite pa in                 rewrite pb in                 Refl
  (Yes pa, No  nb) => rewrite pa in                 rewrite notTrueIsFalse nb in  Refl
  (No  na, Yes pb) => rewrite notTrueIsFalse na in  rewrite pb in                 Refl
  (No  na, No  nb) => rewrite notTrueIsFalse na in  rewrite notTrueIsFalse nb in  Refl

-- ... with complement

export
union_with_its_complement : (s : InSet a) -> s + complement s == Universe
union_with_its_complement s x = rewrite orNotTrue $ s x in Refl

----------------------------
--- Laws of intersection ---
----------------------------

export
intersection_of_self : (s : InSet a) -> s # s == s
intersection_of_self s x = rewrite andSameNeutral $ s x in Refl

export
intersection_commutative : (sa, sb : InSet a) -> sa # sb == sb # sa
intersection_commutative sa sb x = rewrite andCommutative (sa x) (sb x) in Refl

export
intersection_associative : (sa, sb, sc : InSet a) -> sa # (sb # sc) == (sa # sb) # sc
intersection_associative sa sb sc x = rewrite andAssociative (sa x) (sb x) (sc x) in Refl

export
intersection_universe_neutral : (s : InSet a) -> s # Universe == s
intersection_universe_neutral s x = rewrite andTrueNeutral $ s x in Refl

export
intersection_preserves_empty : (s : InSet a) -> s # [] == []
intersection_preserves_empty s x = rewrite andFalseFalse $ s x in Refl

-- ... with union

export
intersection_distributes_over_union : (sa, sb, sc : InSet a) -> sa # (sb + sc) == (sa # sb) + (sa # sc)
intersection_distributes_over_union sa sb sc x = rewrite andDistribOrR (sa x) (sb x) (sc x) in Refl

-- ... with set diff

export
intersection_diff_swap : (sa, sb, sc : InSet a) -> sa # (sb - sc) == sb # (sa - sc)
intersection_diff_swap sa sb sc x = rewrite andAssociative (sa x) (sb x) (not $ sc x) in
                                    rewrite andAssociative (sb x) (sa x) (not $ sc x) in
                                    rewrite andCommutative (sa x) (sb x) in
                                    Refl

export
intersection_diff_assoc : (sa, sb, sc : InSet a) -> sa # (sb - sc) == (sa # sb) - sc
intersection_diff_assoc sa sb sc x = rewrite sym $ andAssociative (sa x) (sb x) (not $ sc x) in Refl

-- ... with symmetrical diff

export
intersection_distributes_over_symdiff : (sa, sb, sc : InSet a) -> sa # (sb ^ sc) == (sa # sb) ^ (sa # sc)
intersection_distributes_over_symdiff sa sb sc x = case decEq (sa x) True of
  Yes pa => rewrite pa in Refl
  No na => rewrite notTrueIsFalse na in Refl

-- ... with complement

export
intersection_with_complement : (sa, sb : InSet a) -> sa # complement sb == sa - sb
intersection_with_complement _ _ _ = Refl

export
intersection_with_its_complement : (s : InSet a) -> s # complement s == []
intersection_with_its_complement s x = rewrite andNotFalse $ s x in Refl

------------------------------
--- Laws of set difference ---
------------------------------

export
diff_of_intersection : (sa, sb, sc : InSet a) -> sc - (sa # sb) == (sc - sa) + (sc - sb)
diff_of_intersection sa sb sc x = rewrite notAndIsOr (sa x) (sb x) in
                                  rewrite andDistribOrR (sc x) (not $ sa x) (not $ sb x) in
                                  Refl

export
diff_of_union : (sa, sb, sc : InSet a) -> sc - (sa + sb) == (sc - sa) # (sc - sb)
diff_of_union sa sb sc x = rewrite notOrIsAnd (sa x) (sb x) in
                           rewrite andAssociative (sc x && not (sa x)) (sc x) (not $ sb x) in
                           rewrite sym $ andAssociative (sc x) (not $ sa x) (sc x) in
                           rewrite andCommutative (not $ sa x) (sc x) in
                           rewrite andAssociative (sc x) (sc x) (not $ sa x) in
                           rewrite andSameNeutral $ sc x in
                           rewrite andAssociative (sc x) (not $ sa x) (not $ sb x) in
                           Refl

export
diff_of_diff : (sa, sb, sc : InSet a) -> sc - (sb - sa) == (sc # sa) + (sc - sb)
diff_of_diff sa sb sc x = rewrite notAndIsOr (sb x) (not $ sa x) in
                          rewrite notInvolutive $ sa x in
                          rewrite orCommutative (not $ sb x) (sa x) in
                          rewrite andDistribOrR (sc x) (sa x) (not $ sb x) in
                          Refl

export
diff_of_self : (s : InSet a) -> s - s == []
diff_of_self s x = andNotFalse $ s x

export
diff_of_empty_left : (s : InSet a) -> [] - s == []
diff_of_empty_left _ _ = Refl

export
diff_of_empty_right : (s : InSet a) -> s - [] == s
diff_of_empty_right s x = andTrueNeutral $ s x

export
diff_of_universe : (s : InSet a) -> s - Universe == []
diff_of_universe s x = andFalseFalse $ s x

export
diff_of_complements : (sa, sb : InSet a) -> complement sa - complement sb == sb - sa
diff_of_complements sa sb x = rewrite andCommutative (sb x) (not $ sa x) in
                              rewrite notInvolutive $ sb x in
                              Refl

--------------------------------------
--- Laws of symmetrical difference ---
--------------------------------------

export
symdiff_as_union_of_diffs : (sa, sb : InSet a) -> sa ^ sb == (sa - sb) + (sb - sa)
symdiff_as_union_of_diffs sa sb x = case (decEq (sa x) True, decEq (sb x) True) of
  (Yes pa, Yes pb) => rewrite pa in                 rewrite pb in                 Refl
  (Yes pa, No  nb) => rewrite pa in                 rewrite notTrueIsFalse nb in  Refl
  (No  na, Yes pb) => rewrite notTrueIsFalse na in  rewrite pb in                 Refl
  (No  na, No  nb) => rewrite notTrueIsFalse na in  rewrite notTrueIsFalse nb in  Refl

export
symdiff_as_diff_of_ui : (sa, sb : InSet a) -> sa ^ sb == (sa + sb) - (sa # sb)
symdiff_as_diff_of_ui sa sb x = case (decEq (sa x) True, decEq (sb x) True) of
  (Yes pa, Yes pb) => rewrite pa in                 rewrite pb in                 Refl
  (Yes pa, No  nb) => rewrite pa in                 rewrite notTrueIsFalse nb in  Refl
  (No  na, Yes pb) => rewrite notTrueIsFalse na in  rewrite pb in                 Refl
  (No  na, No  nb) => rewrite notTrueIsFalse na in  rewrite notTrueIsFalse nb in  Refl

export
symdiff_commutative : (sa, sb : InSet a) -> sa ^ sb == sb ^ sa
symdiff_commutative sa sb x = xorCommutative (sa x) (sb x)

export
symdiff_associative : (sa, sb, sc : InSet a) -> sa ^ (sb ^ sc) == (sa ^ sb) ^ sc
symdiff_associative sa sb sc x = rewrite xorAssociative (sa x) (sb x) (sc x) in Refl

export
symdiff_with_empty : (s : InSet a) -> s ^ [] == s
symdiff_with_empty s x = rewrite xorCommutative (s x) False in
                         rewrite xorFalseNeutral $ s x in
                         Refl

export
symdiff_with_self : (s : InSet a) -> s ^ s == []
symdiff_with_self s x = xorSameFalse $ s x

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
symdiff_of_complements : (sa, sb : InSet a) -> sa ^ sb == complement sa ^ complement sb
symdiff_of_complements sa sb x = rewrite notXorCancel (sa x) (sb x) in Refl

--------------------------
--- Laws of complement ---
--------------------------

export
comp_of_union : (sa, sb : InSet a) -> complement (sa + sb) == complement sa # complement sb
comp_of_union sa sb x = rewrite notOrIsAnd (sa x) (sb x) in Refl

export
comp_of_intersection : (sa, sb : InSet a) -> complement (sa # sb) == complement sa + complement sb
comp_of_intersection sa sb x = rewrite notAndIsOr (sa x) (sb x) in Refl

export
comp_of_empty : complement [] == Universe
comp_of_empty _ = Refl

export
comp_of_universe : complement Universe == []
comp_of_universe _ = Refl

export
comp_involutive : (s : InSet a) -> complement (complement s) == s
comp_involutive s x = rewrite notInvolutive $ s x in Refl

export
comp_of_diff : (sa, sb : InSet a) -> complement (sa - sb) == complement sa + sb
comp_of_diff sa sb x = rewrite notAndIsOr (sa x) (not $ sb x) in
                       rewrite notInvolutive $ sb x in
                       Refl

---------------------------------
--- Laws of cartesian product ---
---------------------------------

-- TODO to add cartesian prodect's laws:
-- Operations over cartesian products at both sides:
--   (A * C) # (B * D) == (A # B) * (C # D)
--   (A * C) \ (B * D) == A * (C - D) + (A - B) * C
--   (A * C) + (B * D) == ((A - B) * C) # ((A # B) * (C + D)) # ((B - A) * D)
-- Distributivity:
--   A * (B # C) = (A # B) * (A # C)
--   A * (B + C) = (A + B) * (A + C)
--   A * (B \ C) = (A \ B) * (A \ C)
--   complement (A * B) = (complement A * complement B) + (complement A * B) + (A * complement B)
-- Subsets of cartesian products
--   A <= B -> A * C <= B * C
--   (x : a ** So (x `isin` A)) -> (y : b ** So (y `isin` B)) -> (A * B) <= (C * D) -> A <= C
--   (x : a ** So (x `isin` A)) -> (y : b ** So (y `isin` B)) -> (A * B) <= (C * D) -> B <= D
--   (x : a ** So (x `isin` A)) -> (y : b ** So (y `isin` B)) -> A <= C -> B <= D -> (A * B) <= (C * D)
