module Chapter4

import Data.InSet
import Data.List

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
to_set_not_surj : Eq a => EqRefl a -> Not $ (f : a -> InSet a) -> Surj f
to_set_not_surj er surj = let SurjPrf f = surj \x => [x] in
                          let (y ** prf) = f [] in
                          non_empty_is_not_empty (y ** x_in_x_etc [] y (er y)) $ sym prf
