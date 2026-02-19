module Modality

%hide (<)
%hide (<=)
%hide (>)
%hide (>=)
%hide Prelude.Ops.infix.(<)
%hide Prelude.Ops.infix.(<=)
%hide Prelude.Ops.infix.(>)
%hide Prelude.Ops.infix.(>=)

export
interface Eq a => PartialOrder a where
  (<) : a -> a -> Maybe Bool

  (<=) : a -> a -> Maybe Bool
  (<=) x y =
    if x == y
       then Just True
       else (<) x y
  (>) : a -> a -> Maybe Bool
  (>) x y = map not ((<=) x y)
  (>=) : a -> a -> Maybe Bool
  (>=) x y =
    if x == y
       then Just True
       else map not ((<) x y)

  export infixl 6 <
  export infixl 6 <=
  export infixl 6 >
  export infixl 6 >=

public export
data TyM : Type -> Type where
  TyUnitM : {0index : Type} -> TyM index
  RawTy : {0index : Type} -> (ty : Type) -> TyM index
  (~>) : {0index : Type} -> TyM index -> TyM index -> TyM index
  (#~>) : {0index : Type} -> (i : index) -> TyM index -> TyM index

export infixr 10 ~>
export infixr 10 #~>

export
translate : PartialOrder index => (i : index) -> TyM index -> Type
translate i TyUnitM = ()
translate i (RawTy ty) = ty
translate i (l ~> r) = (translate i l) -> (translate i r)
translate i (i' #~> r) =
  case i <= i' of
       Just True => translate i r
       _ => ()

