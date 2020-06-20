module Data.Lawful.Eqv

%default total

||| `Eq` enriched with reflexivity, commutativity and transitivity.
public export
interface Eq a => Eqv a where
  0 eqv_refl : (x : a) -> x == x = True
  0 eqv_comm : (x, y : a) -> x == y = y == x
  0 eqv_trans : (x, y, z : a) -> x == y = True -> y == z = True -> x == z = True

export
Eqv () where
  eqv_refl () = Refl
  eqv_comm () () = Refl
  eqv_trans () () () Refl Refl = Refl

export
Eqv Bool where
  eqv_refl True  = Refl
  eqv_refl False = Refl

  eqv_comm True  True  = Refl
  eqv_comm True  False = Refl
  eqv_comm False True  = Refl
  eqv_comm False False = Refl

  eqv_trans True  True  True  Refl Refl = Refl
  eqv_trans False False False Refl Refl = Refl

export
Eqv Nat where
  eqv_refl 0     = Refl
  eqv_refl (S n) = rewrite eqv_refl n in Refl

  eqv_comm 0     0     = Refl
  eqv_comm 0     (S m) = Refl
  eqv_comm (S n) 0     = Refl
  eqv_comm (S n) (S m) = rewrite eqv_comm n m in Refl

  eqv_trans Z Z Z Refl Refl = Refl
  eqv_trans (S n) (S m) (S k) nm mk = eqv_trans n m k nm mk

split_and : {a, b : Bool} -> a && b = True -> (a = True, b = True)
split_and {a=True} {b=True} Refl = (Refl, Refl)

export
Eqv a => Eqv (List a) where
  eqv_refl [] = Refl
  eqv_refl (x::xs) = rewrite eqv_refl x in eqv_refl xs

  eqv_comm [] [] = Refl
  eqv_comm [] (x::xs) = Refl
  eqv_comm (x::xs) [] = Refl
  eqv_comm (x::xs) (y::ys) = rewrite eqv_comm x y in
                             rewrite eqv_comm xs ys in
                             Refl

  eqv_trans [] [] [] Refl Refl = Refl
  eqv_trans (x::xs) (y::ys) (z::zs) xy yz = rewrite eqv_trans x y z (fst $ split_and xy) (fst $ split_and yz) in
                                            eqv_trans xs ys zs (snd $ split_and xy) (snd $ split_and yz)

export
(Eqv a, Eqv b) => Eqv (a, b) where
  eqv_refl (a, b) = rewrite eqv_refl a in
                    rewrite eqv_refl b in
                    Refl

  eqv_comm (a, b) (c, d) = rewrite eqv_comm a c in
                           rewrite eqv_comm b d in
                           Refl

  eqv_trans (a, b) (c, d) (e, f) ac ce = rewrite eqv_trans a c e (fst $ split_and ac) (fst $ split_and ce) in
                                         rewrite eqv_trans b d f (snd $ split_and ac) (snd $ split_and ce) in
                                         Refl

export
(Eqv a, Eqv b) => Eqv (Either a b) where
  eqv_refl (Left x)  = rewrite eqv_refl x in Refl
  eqv_refl (Right y) = rewrite eqv_refl y in Refl

  eqv_comm (Left x)  (Left y)  = rewrite eqv_comm x y in Refl
  eqv_comm (Right x) (Right y) = rewrite eqv_comm x y in Refl
  eqv_comm (Left x) (Right y) = Refl
  eqv_comm (Right x) (Left y) = Refl

  eqv_trans (Left x)  (Left y)  (Left z ) xy yz = eqv_trans x y z xy yz
  eqv_trans (Right x) (Right y) (Right z) xy yz = eqv_trans x y z xy yz
