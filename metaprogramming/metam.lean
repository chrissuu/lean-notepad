import Lean
open Lean Lean.Expr Lean.Meta Nat

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

-- exercise 1
#eval show MetaM Unit from do
  let hi ← Lean.Meta.mkFreshExprMVar (Expr.const `String []) (userName := `hi)
  IO.println s!"value in hi: {← instantiateMVars hi}"

  hi.mvarId!.assign (mkNatLit 3)
  IO.println s!"value in hi: {← instantiateMVars hi}"


-- exercise 2


-- exercise 3
#eval show MetaM Unit from do
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

  -- Create `mvar1` with type `Nat`
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  -- Create `mvar2` with type `Nat`
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  -- Create `mvar3` with type `Nat`
  let mvar3 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar3)

  -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
  mvar1.mvarId!.assign (Lean.mkAppN (Expr.const ``Nat.add []) #[twoExpr, (Lean.mkAppN (Expr.const ``Nat.add []) #[mvar2, mvar3])])

  -- Assign `mvar3` to `1`
  mvar3.mvarId!.assign oneExpr

  -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
  let instantiatedMvar1 ← instantiateMVars mvar1
  IO.println instantiatedMvar1 -- Nat.add (Nat.add 2 ?_uniq.2) 1

-- exercise 4
elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  IO.println "Our metavariable"
  IO.println s!"\n{metavarDecl.userName} : {metavarDecl.type}"

  IO.println "All of its local declarations"
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      IO.println s!"\nImpl. Detail {ldecl.userName} : {ldecl.type}"
      continue
    -- do something with the ldecl
    IO.println s!"\nName: {ldecl.userName}, Type: {ldecl.type}"

-- theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
--   explore
--   sorry

-- exercise 5
elab "solve" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl
  for ldecl in ← getLCtx do
    if ← isDefEq metavarDecl.type ldecl.type then
      mvarId.assign ldecl.toExpr
  IO.println "tactic done!"

set_option linter.unusedVariables false
theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  solve

-- exercise 6

/-
[Computation]
What is the normal form of the following expressions:
a) fun x => x of type Bool → Bool b) (fun x => x)
((true && false) || true) of type Bool c) 800 + 2 of type Nat
-/

-- exercise 7
