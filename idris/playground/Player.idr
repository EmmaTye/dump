module Player

import Data.Fin
import Data.Buffer
import Data.List

record Position where
  constructor MkPosition
  x, y : Int

Eq Position where
  p == q = (p.x == q.x) && (p.y == q.y)
  p /= q = not (p == q)

data Direction = N | E | S | W

data Item = Label String

MAX_INVENTORY : Nat
MAX_INVENTORY = integerToNat 10

data Inventory : (n : Nat) -> Type where
  Empty : Inventory Z
  Add : Item -> Inventory n -> Inventory (S n)

data Player : Type where
  MkPlayer : Position -> Direction -> (items : Fin MAX_INVENTORY) -> Inventory (finToNat items) -> Player

newPlayer : Player
newPlayer = MkPlayer (MkPosition 0 0) N FZ Empty

clockwise : Direction -> Direction
clockwise N = E
clockwise E = S
clockwise S = W
clockwise W = N

turnClockwise : Player -> Player
turnClockwise (MkPlayer pos dir items inventory) = MkPlayer pos (clockwise dir) items inventory

move : Player -> Player
move (MkPlayer pos N items inventory) = MkPlayer ({y $= (+ 1)} pos) N items inventory
move (MkPlayer pos E items inventory) = MkPlayer ({x $= (+ 1)} pos) E items inventory
move (MkPlayer pos S items inventory) = MkPlayer ({y $= ((-) 1)} pos) S items inventory
move (MkPlayer pos W items inventory) = MkPlayer ({x $= ((-) 1)} pos) W items inventory

data Board' : (n : Nat) -> Type where
  EmptyBoard : Board' Z
  AddToBoard : Item -> Position -> Board' n -> Board' (S n)

pNotInAcc : Position -> List Position -> Bool
pNotInAcc pos [] = True
pNotInAcc pos (x :: xs) = (pos /= x) && pNotInAcc pos xs

noDups' : Board' n -> List Position -> Bool
noDups' EmptyBoard _ = True
noDups' (AddToBoard i p b) acc =
     (pNotInAcc p acc) && (noDups' b (p :: acc))

addToBoardPos : (P : ((n : Nat) -> Board' n -> Type)) ->
                P Z EmptyBoard ->
                ((n : Nat) -> (item : Item) -> (position : Position) -> (board : Board' n) -> P n board -> P (S n) (AddToBoard item position board)) ->
                (n : Nat) -> (board : Board' n) -> P n board
addToBoardPos prop base ind Z EmptyBoard = base
addToBoardPos prop base ind (S n) (AddToBoard i p b) = 
  let boardPrev = addToBoardPos prop base ind n b in
      ind n i p b boardPrev



noDupsAdd' : (board : Board' n) -> (seenPos : List Position) ->
             (noDups' board seenPos) -> (pos : Position) ->
             (item : Item) -> (pNotInAcc pos seenPos = True) ->
             (noDups' (AddToBoard item pos board) (pos :: seenPos) = True)
noDupsAdd' EmptyBoard seenPos Refl pos item posNtInAccPf = cong (\p => AddToBoard item p EmptyBoard) posNtInAccPf
noDupsAdd' (AddToBoard item' pos' board) seenPos noDupsPf pos item posNtInAccPf = ?rhs



noDups : Board' n -> Bool
noDups board = noDups' board []

-- noDupsSmallerBoard : (board : Board' (S n) ** noDups board = True) -> (boardDec : Board' n ** noDups boardDec = True)
-- noDupsSmallerBoard (AddToBoard item pos board ** pf) = (board ** cong  pf)

Board : (n : Nat) -> Type
Board n = (b : Board' n ** noDups b = True)

emptyBoard : Board Z
emptyBoard = (EmptyBoard ** Refl)

notOnBoard : Position -> Board n -> Bool
notOnBoard pos (EmptyBoard ** Refl) = True
notOnBoard pos (AddToBoard item pos' board ** p) =
  (pos /= pos') && (notOnBoard pos (board ** Refl))


addToBoard : (item : Item) -> (pos : Position) -> (board : Board n) -> (notOnBoard pos board = True) -> Board (S n)

