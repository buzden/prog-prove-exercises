module Data.InSet.List

import Data.Bool
import Data.InSet
import Data.List

import Syntax.WithProof

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
reverse_preserves_elems (x::xs) n with (@@(decEq n x))
  reverse_preserves_elems (x::xs) n | (eq ** p) = rewrite reverseOfConc x xs in
                                                  rewrite elems_of_concat (reverse xs) [x] n in
                                                  rewrite p in
                                                  case eq of
                                                    Yes yy => rewrite yy in
                                                              rewrite orTrueTrue $ x `isin` elems (reverse xs) in
                                                              Refl
                                                    No _ => rewrite reverse_preserves_elems xs n in
                                                            rewrite orFalseNeutral $ n `isin` elems xs in
                                                            Refl
