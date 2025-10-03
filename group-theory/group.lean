import Mathlib.Data.Set.Basic

class Group (G : Type) where
  star : G → G → G
  one : G
  inv : G → G
  star_assoc : ∀ a b c, star a (star b c) = star (star a b) c
  one_star : ∀ a, star one a = a
  star_one : ∀ a, star a one = a
  star_inv : ∀ a, star a (inv a) = one
  inv_star : ∀ a, star (inv a) a = one

namespace Group
  infixl:70 " * " => star
  notation "e" => one
end Group

structure GroupHomomorphism {G H : Type} [Group G] [Group H] where
  map : G → H
  preserves_star : ∀ a b, map (Group.star a b) = Group.star (map a) (map b)

structure SubGroup {G : Type} [Group G] where
  carrier : Set G
  one_mem : (Group.one : G) ∈ carrier
  inv_mem : (∀ g, g ∈ carrier → Group.inv g ∈ carrier)
  mul_mem : (∀ a b, a ∈ carrier → b ∈ carrier → Group.star a b ∈ carrier)

theorem identity_is_unique
    {G : Type} [Group G]
    (e' : G)
    (h : ∀ a, e' * a = a)
    : e' = (e : G) := by
  have he' : e' * e = e := h e
  rw [Group.star_one e'] at he'
  exact he'

theorem inverse_is_unique
    {G : Type} [Group G]
    (u v : G)
    (h : u * v = e)
    : u = Group.inv v := by
  calc
    u = u * e                   := by rw [Group.star_one u]
    _ = u * (v * (Group.inv v)) := by rw [Group.star_inv v]
    _ = u * v * Group.inv v     := by rw [Group.star_assoc]
    _ = e * Group.inv v         := by rw [h]
    _ = Group.inv v             := by rw [Group.one_star]

theorem left_star_eq
  {G : Type} [Group G]
  (g u v : G)
  (h : u = v)
  : g * u = g * v := by
  calc
    g * u = g * v := by rw [h]

theorem group_hom_preserves_one
  {G H : Type} [Group G] [Group H]
  (φ : GroupHomomorphism) :
  φ.map (e : G) = (e : H) := by
  have h_eq : φ.map (e : G) = φ.map (e : G) := by rfl
  have h : (Group.inv (φ.map e)) * (φ.map e) = (Group.inv (φ.map e)) * (φ.map e) := left_star_eq (Group.inv (φ.map e)) (φ.map e) (φ.map e) h_eq
  rw [Group.inv_star] at h

theorem group_hom_preserves_inv
  {G H : Type} [Group G] [Group H]
  (φ : GroupHomomorphism)
  (g : G) :
  φ.map (Group.inv g) = (Group.inv (φ.map g) : H) := by
  calc
    φ.map (Group.inv g) = (e : H) * (φ.map (Group.inv g)) := by rw [Group.one_star]
                      _ = (Group.inv (φ.map g) * (φ.map g)) * (φ.map (Group.inv g)) := by rw [Group.inv_star]
                      _ = (Group.inv (φ.map g)) * ((φ.map g) * (φ.map (Group.inv g))) := by rw [Group.star_assoc]
                      _ = (Group.inv (φ.map g)) * (φ.map (g * Group.inv g)) := by rw [GroupHomomorphism.preserves_star]
                      _ = (Group.inv (φ.map g)) * (φ.map (e)) := by rw [Group.star_inv]
                      _ = (Group.inv (φ.map g)) * (e : H) := by rw [group_hom_preserves_one]
                      _ = Group.inv (φ.map g) := by rw [Group.star_one]
