module Data.Lawful.Eqv

%default total

||| `Eq` enriched with reflexivity, commutativity and transitivity.
public export
interface Eq a => Eqv a where
  0 eqvReflexive   : (x : a) -> x == x = True
  0 eqvCommutative : (x, y : a) -> x == y = y == x
  0 eqvTransitive  : (x, y, z : a) -> x == y = True -> y == z = True -> x == z = True

export
Eqv () where
  eqvReflexive () = Refl
  eqvCommutative () () = Refl
  eqvTransitive () () () Refl Refl = Refl

export
Eqv Bool where
  eqvReflexive True  = Refl
  eqvReflexive False = Refl

  eqvCommutative True  True  = Refl
  eqvCommutative True  False = Refl
  eqvCommutative False True  = Refl
  eqvCommutative False False = Refl

  eqvTransitive True  True  True  Refl Refl = Refl
  eqvTransitive False False False Refl Refl = Refl

export
Eqv Nat where
  eqvReflexive 0     = Refl
  eqvReflexive (S n) = rewrite eqvReflexive n in Refl

  eqvCommutative 0     0     = Refl
  eqvCommutative 0     (S m) = Refl
  eqvCommutative (S n) 0     = Refl
  eqvCommutative (S n) (S m) = rewrite eqvCommutative n m in Refl

  eqvTransitive Z Z Z Refl Refl = Refl
  eqvTransitive (S n) (S m) (S k) nm mk = eqvTransitive n m k nm mk

split_and : {a, b : Bool} -> a && b = True -> (a = True, b = True)
split_and {a=True} {b=True} Refl = (Refl, Refl)

export
Eqv a => Eqv (List a) where
  eqvReflexive [] = Refl
  eqvReflexive (x::xs) = rewrite eqvReflexive x in eqvReflexive xs

  eqvCommutative [] [] = Refl
  eqvCommutative [] (x::xs) = Refl
  eqvCommutative (x::xs) [] = Refl
  eqvCommutative (x::xs) (y::ys) = rewrite eqvCommutative x y in
                                   rewrite eqvCommutative xs ys in
                                   Refl

  eqvTransitive [] [] [] Refl Refl = Refl
  eqvTransitive (x::xs) (y::ys) (z::zs) xy yz = rewrite eqvTransitive x y z (fst $ split_and xy) (fst $ split_and yz) in
                                                rewrite eqvTransitive xs ys zs (snd $ split_and xy) (snd $ split_and yz) in
                                                Refl

export
(Eqv a, Eqv b) => Eqv (a, b) where
  eqvReflexive (a, b) = rewrite eqvReflexive a in
                        rewrite eqvReflexive b in
                        Refl

  eqvCommutative (a, b) (c, d) = rewrite eqvCommutative a c in
                                 rewrite eqvCommutative b d in
                                 Refl

  eqvTransitive (a, b) (c, d) (e, f) ac ce = rewrite eqvTransitive a c e (fst $ split_and ac) (fst $ split_and ce) in
                                             rewrite eqvTransitive b d f (snd $ split_and ac) (snd $ split_and ce) in
                                             Refl

export
(Eqv a, Eqv b) => Eqv (Either a b) where
  eqvReflexive (Left x)  = rewrite eqvReflexive x in Refl
  eqvReflexive (Right y) = rewrite eqvReflexive y in Refl

  eqvCommutative (Left x)  (Left y)  = rewrite eqvCommutative x y in Refl
  eqvCommutative (Right x) (Right y) = rewrite eqvCommutative x y in Refl
  eqvCommutative (Left x) (Right y) = Refl
  eqvCommutative (Right x) (Left y) = Refl

  eqvTransitive (Left x)  (Left y)  (Left z ) xy yz = eqvTransitive x y z xy yz
  eqvTransitive (Right x) (Right y) (Right z) xy yz = eqvTransitive x y z xy yz
