import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Disjoint

class DownTreeLike (α : Type*) [LE α] where
  le_or_le_of_le_of_le {a b c : α} : a ≤ b → a ≤ c → b ≤ c ∨ c ≤ b

open Set

lemma DownTreeLike.Iic_cases {α : Type*} [Preorder α] [DownTreeLike α] (b c : α) :
    Disjoint (Iic b) (Iic c) ∨ Iic b ⊆ Iic c ∨ Iic c ⊆ Iic b := by
  rw [Classical.or_iff_not_imp_left, Set.not_disjoint_iff, Iic_subset_Iic, Iic_subset_Iic]
  intro ⟨x, (hb : x ≤ b), (hc : x ≤ c)⟩
  exact le_or_le_of_le_of_le hb hc
