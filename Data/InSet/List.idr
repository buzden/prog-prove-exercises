module Data.InSet.List

import Data.Bool
import Data.InSet
import Data.List

import Syntax.WithProof

%default total

public export
elems : Equality a => List a -> InSet a
elems []      = []
elems (x::xs) = x :: elems xs

export
elems_of_concat : Equality a => (xs, ys : List a) -> elems (xs ++ ys) == elems xs + elems ys
elems_of_concat [] _ _ = Refl
elems_of_concat (x::xs) ys n = case @@(n =?= x) of
  (True  ** prf) => rewrite prf in Refl
  (False ** prf) => rewrite prf in elems_of_concat xs ys n

-- This is better to be placed in `Data.List`.
reverseOfConc : (x : a) -> (xs : List a) -> reverse (x::xs) = reverse xs ++ [x]
reverseOfConc x []      = Refl
reverseOfConc x (y::ys) = rewrite reverseOfConc y ys in
                          rewrite sym $ appendAssociative (reverse ys) [y] [x] in
                          rewrite revAppend [x, y] ys in
                          Refl

export
reverse_preserves_elems : Equality a => (xs : List a) -> elems (reverse xs) == elems xs
reverse_preserves_elems []      n = Refl
reverse_preserves_elems (x::xs) n = rewrite reverseOfConc x xs in
                                    rewrite elems_of_concat (reverse xs) [x] n in
                                    case @@(n =?= x) of
                                      (True ** prf) => rewrite x_in_same_etc n x [] prf in
                                                       rewrite prf in
                                                       rewrite orTrueTrue $ n `isin` elems (reverse xs) in
                                                       Refl
                                      (False ** prf) => rewrite prf in
                                                        rewrite reverse_preserves_elems xs n in
                                                        rewrite orFalseNeutral $ n `isin` elems xs in
                                                        Refl
