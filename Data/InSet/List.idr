module Data.InSet.List

import Data.Bool
import Data.InSet
import Data.List
import Decidable.Equality

%default total

public export
elems : DecEq a => List a -> InSet a
elems []      = []
elems (x::xs) = x :: elems xs

export
elems_of_concat : DecEq a => (xs, ys : List a) -> elems (xs ++ ys) == elems xs + elems ys
elems_of_concat [] _ _ = Refl
elems_of_concat (y::ys) zs x with (decEq x y)
  elems_of_concat (_::_)  _  _ | Yes yy = Refl
  elems_of_concat (_::ys) zs x | No  nn = elems_of_concat ys zs x

-- This is better to be placed in `Data.List`.
reverseOfConc : (x : a) -> (xs : List a) -> reverse (x::xs) = reverse xs ++ [x]
reverseOfConc x []      = Refl
reverseOfConc x (y::ys) = rewrite reverseOfConc y ys in
                          rewrite sym $ appendAssociative (reverse ys) [y] [x] in
                          rewrite revAppend [x, y] ys in
                          Refl

export
reverse_preserves_elems : DecEq a => (xs : List a) -> elems (reverse xs) == elems xs
reverse_preserves_elems []      n = Refl
reverse_preserves_elems (x::xs) n with (decEq n x)
  reverse_preserves_elems (x::xs) n | Yes yy = rewrite reverseOfConc x xs in
                                               rewrite elems_of_concat (reverse xs) [x] n in
                                               rewrite yy in
                                               rewrite x_in_x_etc x [] in
                                               rewrite orTrueTrue $ x `isin` elems (reverse xs) in
                                               Refl
  reverse_preserves_elems (x::xs) n | No nn = rewrite reverseOfConc x xs in
                                              rewrite elems_of_concat (reverse xs) [x] n in
                                              rewrite not_x_not_in_x_etc n x nn in
                                              rewrite reverse_preserves_elems xs n in
                                              rewrite orFalseNeutral $ n `isin` elems xs in
                                              Refl

  -- TODO to move out the common prefix of the two cases of the proof
