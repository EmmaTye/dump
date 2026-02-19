-- We want to replace instances of (Vect n a) as (List a) at runtime,
-- i.e. remove the index n
-- We do this by giving an isomorphic ~representation~ of (Vect n a)
-- as a dependent pair of a (List a) (i.e. our chosen runtime representation)
-- and a proof that the given list satisfies the inductive properties of
-- (Vect n a).
-- We also need to be able to eliminate (induct) over the new representation
-- in the same structural way as (Vect n a) so that pattern matching can be
-- re-used.

module InductiveFamilies

import Data.Vect

-- Our representation of (Vect n a) as a (List a) and
-- a proof that it satisfies the constraints of (Vect n a)
List' : (n : Nat) -> (a : Type) -> Type
List' n a = (xs : List a ** length xs = n)

-- Smart constructors
Nil' : List' Z a
Nil' = ([] ** Refl)

(<::>) : a -> List' n a -> List' (S n) a
(<::>) x (xs ** p) = (x :: xs ** cong S p)

export infixr 10 <::>

data List'View : List' n a -> Type where
  Nil'V : List'View Nil'
  (<::*>) : (x : a) -> (xs : List' n a) -> List'View (x <::> xs)

export infixr 10 <::*>

view : (xs : List' n a) -> List'View xs
view ([] ** Refl) = Nil'V
view ((x :: xs) ** Refl) = x <::*> (xs ** Refl)

-- eliminator for List' that follows the same structure as Vect
elimList' : (P : (n : Nat) -> List' n a -> Type)
  -> P Z Nil'
  -> ((x : a) -> (n : Nat) -> (xs : List' n a) -> P n xs -> P (S n) (x <::> xs))
  -> (n : Nat) -> (xs : List' n a) -> P n xs
elimList' prop base ind n l with (view l)
  elimList' prop base ind Z _ | Nil'V = base
  elimList' prop base ind (S n) _ | (x <::*> xs) =
    let
      recProof = elimList' prop base ind n xs
    in
    ind x n xs recProof

-- proofs that elimList' follows the same structure as Vect
elimList'nilId : elimList' prop base ind Z (Nil') = base
elimList'nilId = Refl
elimList'consId : (prop : (n : Nat) -> List' n a -> Type) ->
                  (base : prop Z Nil') ->
                  (ind : (x : a) -> (n : Nat) -> (xs : List' n a) -> prop n xs -> prop (S n) (x <::> xs)) ->
                  (n : Nat) -> (x : a) -> (xs : List' n a) ->
                  (elimList' prop base ind (S n) (x <::> xs) = ind x n xs (elimList' prop base ind n xs))
-- elimList'consId prop base ind n x xs with (view xs)
--   elimList'consId prop base ind Z x _ | Nil'V = Refl
--   elimList'consId prop base ind (S n) x _ | (y <::*> xs) =
--     let rec = elimList'consId prop base ind n y xs in
--         rewrite rec in Refl

repr : Vect n a -> List' n a
repr [] = Nil'
repr (x :: xs) = 
  let ys = repr xs in
      x <::> ys

unrepr : List' n a -> Vect n a
unrepr l with (view l)
  unrepr _ | Nil'V = []
  unrepr _ | (x <::*> xs) =
    let ys = unrepr xs in
        x :: ys
-- unrepr (xs ** Refl) = fromList xs

record Repr (a : Type) (b : Type) where
  constructor MkRepr
  repr : a -> b
  unrepr : b -> a
  reprEta1 : (t : a) -> unrepr (repr t) = t
  reprEta2 : (s : b) -> repr (unrepr s) = s


reprVectAsList' : Repr (Vect n a) (List' n a)
-- reprVectAsList' = MkRepr repr unrepr (\x => Refl) (\x => Refl)



