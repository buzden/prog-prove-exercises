module Data.InSet.List

import Data.Bool
import Data.InSet
import Data.List
import Decidable.Equality

%default total

public export
elems : Eq a => List a -> InSet a
elems []      = []
elems (x::xs) = x :: elems xs

export
elems_of_concat : Eq a => (xs, ys : List a) -> elems (xs ++ ys) == elems xs + elems ys
elems_of_concat [] _ _ = Refl
elems_of_concat (y::ys) zs x with (x == y)
  elems_of_concat (_::_)  _  _ | True  = Refl
  elems_of_concat (_::ys) zs x | False = elems_of_concat ys zs x

-- This is better to be placed in `Data.List`.
reverseOfConc : (x : a) -> (xs : List a) -> reverse (x::xs) = reverse xs ++ [x]
reverseOfConc x []      = Refl
reverseOfConc x (y::ys) = rewrite reverseOfConc y ys in
                          rewrite sym $ appendAssociative (reverse ys) [y] [x] in
                          rewrite revAppend [x, y] ys in
                          Refl

export
reverse_preserves_elems : Eq a => (xs : List a) -> elems (reverse xs) == elems xs
reverse_preserves_elems []      n = Refl
reverse_preserves_elems (x::xs) n = rewrite reverseOfConc x xs in
                                    rewrite elems_of_concat (reverse xs) [x] n in
                                    rewrite union_commutative (elems (reverse xs)) (elems [x]) n in
                                    rewrite reverse_preserves_elems xs n in
                                    case decEq (n == x) True of
                                      Yes pnx => rewrite pnx in Refl
                                      No nnx  => rewrite notTrueIsFalse nnx in Refl
