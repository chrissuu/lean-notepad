/-
Author:              Chris Su
Date:                Oct 7, 2025
Program Name:        Puzzle solution for math.inc

LinkedIn:            linkedin.com/in/chrissuu
GitHub:              github.com/chrissuu
Personal Website:    chrissuu.com
Email:               chrissu@andrew.cmu.edu
-/

/-
math.inc

Suppose that today is June 1, 2025. We call a date "square" if all of its components
(day, month, and year) are perfect squares. I was born in the last millennium,
and my next birthday (relative to that date) will be the last square date in my
life. If you sum the square roots of the components of that upcoming square birthday
(day, month, year), you obtain my age on June 1, 2025. My mother would have been born
on a square date if the month were a square number; in reality it is not a square date,
but both the month and day are perfect cubes. When was I born, and when was my mother born?
-/

import Mathlib.Tactic
open Nat
open List

structure Date where
  month : Nat
  day : Nat
  year : Nat
  deriving Repr

-- do you know someone older than 150 years old?
def max_human_lifespan : Nat := 150

def today : Date := ⟨ 6, 1, 2025 ⟩

def is_square (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

def is_square_b (n : Nat) : Bool :=
  let k := sqrt n
  n == k * k

def is_square_date (date : Date) : Prop :=
  is_square date.day ∧ is_square date.month ∧ is_square date.year

def is_square_date_b (date : Date) : Bool :=
  is_square_b date.day && is_square_b date.month && is_square_b date.year

def is_cubic (n : Nat) : Prop :=
  ∃ k : Nat, k * k * k = n

def next_birthdate (birthdate : Date) (today : Date) : Date :=
  let same_year := { birthdate with year := today.year }
  if today.month < birthdate.month ∨
     (today.month = birthdate.month ∧ today.day < birthdate.day) then
    same_year
  else
    { same_year with year := today.year + 1 }

def date_is_in_last_millenium (date : Date) : Prop :=
  1001 ≤ date.year ∧ date.year ≤ 2000

def is_last_date_in_container (date : Date) (dates : List Date) (c : Date -> Date -> Bool) : Prop :=
  date ∈ dates ∧ (∀ x ∈ dates, c x date ∨ x = date)

def month_num_day_pairs : List (Nat × Nat) :=
  [
    (1, 31),
    (2, 28),
    (3, 31),
    (4, 30),
    (5, 31),
    (6, 30),
    (7, 31),
    (8, 31),
    (9, 30),
    (10, 31),
    (11, 30),
    (12, 31)
  ]

def month_day_pairs : List (Nat × Nat) :=
  month_num_day_pairs >>= fun (month, num_days) =>
    (List.range' 1 (num_days + 1)).filter (λ n => is_square_b n) |>.map (fun day => (month, day))

def list_cross_product3 (A : List α) (B : List β) (C : List γ) : List (α × β × γ) :=
  A >>= fun a =>
    B >>= fun b =>
      C >>= fun c => [(a, b, c)]

-- Gets dates inclusive <date_left> and exclusive <date_right>, [<date_left>, <date_right>)
def get_dates_in_range (date_left : Date) (date_right : Date) : List Date :=
  let year_count := date_right.year - date_left.year + 1
  let years := List.range' date_left.year year_count -- produces date_left.year .. date_right.year
  month_day_pairs >>= fun (month, day) =>
    years |> List.map (fun y => { month := month, day := day, year := y : Date })

def get_square_dates_in_range (date_left : Date) (date_right : Date) : List Date :=
  List.filter (λ date => is_square_date_b date) (get_dates_in_range date_left date_right)

def date_le (x y : Date) : Prop :=
  x.year < y.year ∨ (x.year = y.year ∧ (x.month < y.month ∨ (x.month = y.month ∧ x.day ≤ y.day)))

instance : DecidableRel date_le := by
  intro x y
  dsimp [date_le]
  infer_instance

def is_my_birthdate (my_birthdate : Date) (today : Date) : Prop :=
  let my_next_birthdate := next_birthdate my_birthdate today
  let years_left_from_today := max_human_lifespan - (today.year - my_birthdate.year)
  let my_life_upper_bound := { my_birthdate with year := today.year + years_left_from_today}
  let next_square_dates_in_lifespan := get_square_dates_in_range today my_life_upper_bound
  let date_le_b := (λ x => (λ y => decide (date_le x y)))

  (date_is_in_last_millenium my_birthdate)
  ∧ (is_last_date_in_container my_next_birthdate next_square_dates_in_lifespan date_le_b)
  ∧ (today.year = my_birthdate.year + (sqrt my_next_birthdate.year + sqrt my_birthdate.month + sqrt my_birthdate.day))

def is_mothers_birthday (mothers_birthdate : Date) : Prop :=
  (is_square mothers_birthdate.month → is_square_date mothers_birthdate)
  ∧ (¬ (is_square mothers_birthdate.day))
  ∧ (is_cubic mothers_birthdate.day)
  ∧ (is_cubic mothers_birthdate.month)

def my_birthdate : Date := ⟨ 9, 25, 1972 ⟩

theorem my_birthdate_is_9_25_1972 : is_my_birthdate my_birthdate today := by
  rw [is_my_birthdate]
  constructor
  . rw [date_is_in_last_millenium]
    decide
  . constructor
    . rw [is_last_date_in_container]
      simp
      rw [next_birthdate] at *
      simp
      constructor
      . rw [get_square_dates_in_range]
        rw [get_dates_in_range]
        simp
        constructor
        . use my_birthdate.month
          use my_birthdate.day
          constructor
          . decide
          . use today.year
            simp
            decide
        . decide
      . rw [get_square_dates_in_range]
        rw [get_dates_in_range]
        simp
        intro date
        intro month
        intro day
        intro h
        intro year_ub
        intro year_leq_year_ub
        intro year_ub_leq_max
        intro h_date
        intro is_square_date
        let birthday_this_year := { my_birthdate with year := today.year }
        let birthday_next_year := { my_birthdate with year := today.year + 1}
        have h_birthday_this_year : birthday_this_year = { month := my_birthdate.month, day := my_birthdate.day, year := today.year} := by rfl
        have h_birthday_next_year : birthday_next_year = { month := my_birthdate.month, day := my_birthdate.day, year := today.year + 1 } := by rfl
        rw [← h_birthday_this_year]
        rw [← h_birthday_next_year]
        right
        by_cases h_today_leq : today.month < my_birthdate.month ∨ today.month = my_birthdate.month ∧ today.day < my_birthdate.day
        rw [← h_date]

    . decide
