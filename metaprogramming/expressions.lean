import Lean

open Lean Nat

def z' := Expr.const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

def one := Expr.app (.const ``Nat.succ []) z
#eval one
-- Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])

def natExpr: Nat → Expr
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)


def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

def constZero : Expr :=
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default

-- lambda which takes x, of type nat, and returns 0?

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelZero, levelZero])
    #[nat, nat, addOne, .app (.const ``List.nil [levelZero]) nat]

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
-- List.map (fun x => Nat.add x 1) [] : List Nat

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil
-- @List.map.{0, 0} Nat Nat (fun x => x.add 1) (@List.nil.{0} Nat) : List.{0} Nat

#reduce mapAddOneNil
-- []

-- Exercises

def exercise_1 : Expr :=
  .app (.app (.const ``Nat.add []) (mkNatLit 1)) (mkNatLit 2)

def exercise_2 : Expr := mkAppN (.const ``Nat.add []) #[mkNatLit 1, mkNatLit 2]

def exercise_3 : Expr :=
  .lam `x nat (mkAppN (.const ``Nat.add []) #[mkNatLit 1, .bvar 0]) BinderInfo.default

def exercise_4 : Expr :=
  .lam `a nat (
    .lam `b nat (
      .lam `c nat (
        mkAppN (.const ``Nat.add []) #[
          (mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2]), .bvar 0
        ]) BinderInfo.default)
      BinderInfo.default)
    BinderInfo.default

elab "exercise_4" : term => return exercise_4
#check exercise_4

-- fun a b c ↦ (b.mul a).add c : Nat → Nat → Nat → Nat

def exercise_10 : Expr :=
  Expr.sort (Nat.toLevel 7)

elab "exercise_10" : term => return exercise_10
#check exercise_10
