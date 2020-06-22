module Chapter4

import Data.InSet
import Data.List

%default total

-- Section 4.1

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

-- Exercise 4.1

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

-- Exercise 4.2

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
