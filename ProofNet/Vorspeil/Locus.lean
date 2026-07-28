import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image

open Function List

abbrev Locus := List ℕ

namespace Locus

/-- A sublocus is an extension. -/
def IsSublocus (ζ ξ : Locus) : Prop := swap IsPrefix ζ ξ

instance : LE Locus := ⟨IsSublocus⟩
instance : IsPartialOrder Locus (· ≤ ·) :=
  inferInstanceAs (IsPartialOrder (List ℕ) <| Function.swap List.IsPrefix)
instance : PartialOrder Locus where
  le_refl := refl
  le_antisymm _ _ h h' := antisymm h h'
  le_trans a b c h h' := IsTrans.trans _ _ _ h h'
  lt a b := a ≤ b ∧ ¬ b ≤ a

def Disjoint (ζ ξ : Locus) : Prop := ¬ ζ ≤ ξ ∧ ¬ ξ ≤ ζ

def concat (ζ : Locus) (i : ℕ) : Locus := ζ ++ [i]

lemma concat_le (ζ : Locus) (i : ℕ) : ζ.concat i ≤ ζ := ⟨[i], rfl⟩

def mconcat (ζ : Locus) (J : Finset ℕ) : Finset Locus := J.image ζ.concat

instance : OrderTop Locus where
  top := []
  le_top ζ := ⟨ζ, rfl⟩

lemma cons_le_cons (i : ℕ) {ζ ξ : Locus} (h : ζ ≤ ξ) : (i :: ζ) ≤ (i :: ξ) := by
  obtain ⟨ξ', rfl⟩ := h
  rw [←List.cons_append]
  exact ⟨ξ', rfl⟩

def commonPref : Locus → Locus → Locus
  | [], _ => []
  | _, [] => []
  | i :: ζ, j :: ξ => if i = j then i :: commonPref ζ ξ else []

@[simp] lemma nil_commonPref (ξ : Locus) : commonPref [] ξ = [] := rfl

@[simp] lemma commonPref_nil (ζ : Locus) : commonPref ζ [] = [] := by cases ζ <;> rfl

@[simp] lemma commonPref_cons_self (i : ℕ) (ζ ξ : Locus) :
  commonPref (i :: ζ) (i :: ξ) = i :: commonPref ζ ξ := by simp [commonPref]

lemma commonPref_cons_eq {i j : ℕ} (h : i = j) (ζ ξ : Locus) :
  commonPref (i :: ζ) (j :: ξ) = i :: commonPref ζ ξ := by simp [commonPref, h]

lemma commonPref_cons_ne {i j : ℕ} (h : i ≠ j) (ζ ξ : Locus) :
  commonPref (i :: ζ) (j :: ξ) = [] := by simp [commonPref, h]

@[simp] lemma commonPref_append_append (ζ ξ' ξ : Locus) :
    commonPref (ζ ++ ξ) (ζ ++ ξ') = ζ ++ commonPref ξ ξ' := by
  induction ζ with
  | nil => simp
  | cons => simpa

instance : SemilatticeSup Locus where
  sup := commonPref
  le_sup_left ζ ξ := by
    induction ζ generalizing ξ
    case nil => rfl
    case cons i ζ ih =>
      cases ξ
      case nil => exact le_top
      case cons j ξ =>
        by_cases h : i = j
        · rw [commonPref_cons_eq h]
          exact cons_le_cons i (ih ξ)
        · rw [commonPref_cons_ne (by grind)]
          exact le_top
  le_sup_right ζ ξ := by
    induction ξ generalizing ζ
    case nil => rw [commonPref_nil]
    case cons i ξ ih =>
      cases ζ
      case nil => exact le_top
      case cons j ζ =>
        by_cases h : i = j
        · rw [commonPref_cons_eq h.symm, h]
          exact cons_le_cons j (ih ζ)
        · rw [commonPref_cons_ne (by grind)]
          exact le_top
  sup_le ζ ζ' ξ h h' := by
    obtain ⟨ζ, rfl⟩ := h
    obtain ⟨ζ', rfl⟩ := h'
    simpa using ⟨commonPref ζ ζ', rfl⟩


end Locus
