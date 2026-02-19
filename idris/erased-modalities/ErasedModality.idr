module ErasedModality

import Modality

-- send a value from l to l'
-- when translated in the context of l, this will become
-- ty -> () (an operation sending a value)
-- and when translated in the context of l', this will become
-- () -> ty (an operation receiving a value)
sendTy : {0location : Type} -> 
         (l : location) ->
         (l' : location) ->
         (ty : TyM location) ->
         TyM location
sendTy l l' ty =
  (l #~> ty) ~> (l' #~> ty)

-- lift a function into a specific location
locallyTy : {0location : Type} ->
            (a : TyM location) ->
            (b : TyM location) ->
            (l : location) ->
            TyM location
locallyTy a b l =
  (a ~> b) ~> (l #~> a) ~> (l #~> b)

