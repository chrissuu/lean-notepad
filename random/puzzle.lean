-- Author: Chris Su
-- Date: Oct 7, 2025
-- Program Name: Puzzle solution for math.inc

-- Suppose that today is June 1, 2025. We call a date "square" if all of its components
-- (day, month, and year) are perfect squares. I was born in the last millennium,
-- and my next birthday (relative to that date) will be the last square date in my
-- life. If you sum the square roots of the components of that upcoming square birthday
-- (day, month, year), you obtain my age on June 1, 2025. My mother would have been born
-- on a square date if the month were a square number; in reality it is not a square date,
-- but both the month and day are perfect cubes. When was I born, and when was my mother born?
import Mathlib

structure Date where
  month : Nat
  day : Nat
  year : Nat
  deriving Repr

def today : Date := ⟨ 6, 1, 2025 ⟩

def is_square (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

def is_cubic (n : Nat) : Prop :=
  ∃ k : Nat, k * k * k = n

theorem one_is_square : is_square 1 := by
  use 1
  simp
