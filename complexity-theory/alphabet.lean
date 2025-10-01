inductive Symbol
| blank
| a
| b
deriving Repr, DecidableEq


structure Tape where
  left : List Symbol
  head : Symbol
  right : List Symbol
deriving Repr


inductive Direction
| L | R
deriving Repr


inductive State
| q_initial
| q_curr
| q_accept
| q_reject


def Transition := State × Symbol → Option (State × Symbol × Direction)


def move (t : Tape) (d : Direction) : Tape :=
  match d with
  | Direction.L =>
    match t.left.reverse with
    | []       => { left := [], head := Symbol.blank, right := t.head :: t.right }
    | h :: tl  => { left := tl.reverse, head := h, right := t.head :: t.right }
  | Direction.R =>
    match t.right with
    | []       => { left := t.head :: t.left, head := Symbol.blank, right := [] }
    | h :: tl  => { left := t.head :: t.left, head := h, right := tl }
