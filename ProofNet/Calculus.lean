import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.AddSub

namespace MLL

universe u

variable {Atom : Type*}

@[grind cases]
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | atomDual : Atom → Formula Atom
  | tensor : Formula Atom → Formula Atom → Formula Atom
  | parr : Formula Atom → Formula Atom → Formula Atom

scoped infix:100 " ⊗ " => Formula.tensor
scoped infix:95 " ⅋ " => Formula.parr

def Formula.dual : Formula Atom → Formula Atom
  | atom x => atomDual x
  | atomDual x => atom x
  | tensor A B => parr A.dual B.dual
  | parr A B => tensor A.dual B.dual

@[simp, grind =]
lemma Formula.dual_dual (A : Formula Atom) : A.dual.dual = A := by
  induction A <;> simp_all [dual]

abbrev Sequent (Atom : Type*) := Multiset (Formula Atom)

inductive Paraproof : Sequent Atom → Type _ where
  | daimon (Γ : Sequent Atom) : Paraproof Γ
  | tensor (A B : Formula Atom) (Γ Δ : Sequent Atom) :
      Paraproof (A ::ₘ Γ) → Paraproof (B ::ₘ Δ) → Paraproof (A ⊗ B ::ₘ (Γ + Δ))
  | parr (A B : Formula Atom) (Γ : Sequent Atom) :
      Paraproof (A ::ₘ B ::ₘ Γ) → Paraproof (A ⅋ B ::ₘ Γ)
  | cut (A : Formula Atom) (Γ Δ : Sequent Atom) :
      Paraproof (A ::ₘ Γ) → Paraproof (A.dual ::ₘ Δ) → Paraproof (Γ + Δ)

end MLL
