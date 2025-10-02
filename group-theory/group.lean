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

-- theorem group_hom_preserves_inv
--   {G H : Type} [Group G] [Group H]
--   (φ : GroupHomomorphism)
--   (g : G) :
--   φ.map (Group.inv g) = Group.inv (φ.map g) := by
--   calc
--     φ.map (Group.inv g) = φ.map ()



-- theorem group_hom_preserves_one
--   {G H : Type} [Group G] [Group H]
--   (φ : GroupHomomorphism) :
--   φ.map (e : G) = (e : H) := by
--   calc
--     φ.map (e) = φ.map (e * e) := by rw [Group.one_star e]
--     _             = (φ.map (e * (Group.inv e) * e)) := by rw [Group.star_inv e]
--     _             = (φ.map (e * (Group.inv e)) * (φ.map e)) := by rw [GroupHomomorphism.preserves_star]
--     _ = (φ.map (e) * (φ.map (Group.inv e)) * (φ.map e)) := by rw [GroupHomomorphism.preserves_star]
