import Mathlib.Data.Set.Basic

structure MyGroup (α : Type) where
  (carrier : Set α)
  (mul : α → α → α)
  (one : α)
  (inv : α → α)
  (mul_closed : ∀ a b, a ∈ carrier → b ∈ carrier → mul a b ∈ carrier)
  (mul_assoc : ∀ a b c, a ∈ carrier → b ∈ carrier → c ∈ carrier →
    mul a (mul b c) = mul (mul a b) c)
  (one_mul : ∀ a, a ∈ carrier → mul one a = a)
  (mul_one : ∀ a, a ∈ carrier → mul a one = a)
  (mul_inv : ∀ a, a ∈ carrier → mul a (inv a) = one)
  (inv_mul : ∀ a, a ∈ carrier → mul (inv a) a = one)

structure GroupHom {α β: Type} (G : Group α) (H : Group β) where
