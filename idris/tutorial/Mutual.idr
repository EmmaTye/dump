module Mutual

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

mutual
  -- this compiles even though calling it with a non-zero number hangs
  throwTo : Nat -> Bool
  throwTo Z = True
  throwTo k = throwFrom k

  throwFrom : Nat -> Bool
  throwFrom Z = False
  throwFrom k = throwTo k

data Even : Nat -> Type
data Odd : Nat -> Type

data Even : Nat -> Type where
  ZIsEven : Even Z
  SkIsEven : Odd k -> Even (S k)

data Odd : Nat -> Type where
  SkIsOdd : Even k -> Odd (S k)

data V : Type

T : V -> Type

data V : Type where
  N : V
  Pi : (a : V) -> (T a -> V) -> V

