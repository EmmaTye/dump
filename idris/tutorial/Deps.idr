module Deps

isSingleton : Bool -> Type -> Type
isSingleton False t = List t
isSingleton True t = t

data Vec : Nat -> Type -> Type where
  Nil : Vec Z a
  (::) : a -> Vec k a -> Vec (S k) a

(++) : Vec k a -> Vec n a -> Vec (k + n) a
(++) Nil ys = ys
(++) ((::) x xs) ys = x :: (++) xs ys

data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)

index : forall a, n . (i : Fin n) -> (xs : Vec n a) -> a
index FZ (x::xs) = x
-- index ?fsetlhs (x::xs) = index ?fsetrhs xs
index (FS fset) (x::xs) = index fset xs

