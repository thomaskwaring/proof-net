import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import ProofNet.Formula

namespace MLL

variable {Atom : Type*}

-- -- is carrying around `Fintype` useful / necessary?
-- inductive Paraproof : {α : Type*} → [Fintype α] → Sequent Atom α → Type _ where
--   | daimon {α} [Fintype α] (Γ : Sequent Atom α) : Paraproof Γ
--   | tensor {α β} [Fintype α] [Fintype β] (A B : Formula Atom) (Γ : Sequent Atom α)
--       (Δ : Sequent Atom β) :
--       Paraproof (Γ.cons A) → Paraproof (Δ.cons B) → Paraproof (Γ.sum Δ |>.cons (A ⊗ B))
--   | parr {α} [Fintype α] (A B : Formula Atom) (Γ : Sequent Atom α) :
--       Paraproof (Γ.cons A |>.cons B) → Paraproof (Γ.cons (A ⅋ B))
--   | cut {α β} [Fintype α] [Fintype β] (A : Formula Atom) (Γ : Sequent Atom α)
--       (Δ : Sequent Atom β) :
--       Paraproof (Γ.cons A) → Paraproof (Δ.cons A.dual) → Paraproof (Γ.sum Δ)
--   | exch {α β} [Fintype α] [Fintype β] (f : β ≃ α) (Γ : Sequent Atom α) :
--       Paraproof Γ → Paraproof (Γ.map f)

inductive CutFreeParaproof : {α : Type*} → Sequent Atom α → Type _ where
  | daimon {α} (Γ : Sequent Atom α) : CutFreeParaproof Γ
  | tensor {α β} (A B : Formula Atom) (Γ : Sequent Atom α)
      (Δ : Sequent Atom β) : CutFreeParaproof (Γ.cons A) → CutFreeParaproof (Δ.cons B) →
        CutFreeParaproof (Γ.sum Δ |>.cons (A ⊗ B))
  | parr {α} (A B : Formula Atom) (Γ : Sequent Atom α) :
      CutFreeParaproof (Γ.cons A |>.cons B) → CutFreeParaproof (Γ.cons (A ⅋ B))
  | exch {α β} (f : β ≃ α) (Γ : Sequent Atom α) :
      CutFreeParaproof Γ → CutFreeParaproof (Γ.map f)

end MLL
