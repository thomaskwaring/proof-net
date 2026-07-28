import ProofNet.Calculus
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import ProofNet.ForMathlib.Partition.Map

namespace MLL

variable {Atom : Type*} {α β : Type*}

open Formula Set Sequent Partition

def Formula.PartialTree.size : {A : Formula Atom} → A.PartialTree → ℕ
  | _, leaf A => 1
  | _, parr A B => A.size + B.size + 1
  | _, tensor A B => A.size + B.size + 1

def Sequent.PartialTree.size [Fintype α] {Γ : Sequent Atom α} (Ξ : Γ.PartialTree) : ℕ :=
  Finset.univ.sum fun a => (Ξ a).size

variable {Γ : Sequent Atom α} {Δ : Sequent Atom β} {A B : Formula Atom}

structure ProofStruct (Γ : Sequent Atom α) where
  Ξ : Γ.PartialTree
  axs : Partition (.univ : Set Ξ.Occ)

def ProofStruct.daimon (Γ : Sequent Atom α) : ProofStruct Γ where
  Ξ a := .leaf (Γ a)
  axs := ⊤

def ProofStruct.tensor (P : ProofStruct <| Γ.cons A) (Q : ProofStruct <| Δ.cons B) :
    ProofStruct ((Γ.sum Δ).cons (A ⊗ B)) where
  Ξ := ((P.Ξ.map Option.some).sum (Q.Ξ.map Option.some)).cons <| (P.Ξ none).tensor (Q.Ξ none)
  axs := by
    refine mapEquiv (PartialTree.tensorOccEquiv ..) <|
      (P.axs.mapEquiv <| P.Ξ.extEquiv _ ?_).sumUniv
      (Q.axs.mapEquiv <| Q.Ξ.extEquiv _ ?_)
    · intro a p; cases a <;> simp [PartialTree.cons] <;> rfl
    · intro a p; cases a <;> simp [PartialTree.cons] <;> rfl

def ProofStruct.parr (P : ProofStruct <| (Γ.cons A).cons B) : ProofStruct (Γ.cons <| A ⅋ B) where
  Ξ := (P.Ξ.map Option.some).map (Option.some) |>.cons <| (P.Ξ <| some none).parr (P.Ξ none)
  axs := by
    refine (P.axs.mapEquiv (P.Ξ.extEquiv _ ?_)).mapEquiv (PartialTree.parrOccEquiv ..)
    intro a p; rcases a with _ | (_ | a) <;> simp [PartialTree.cons] <;> rfl

def ProofStruct.exch (f : β ≃ α) (P : ProofStruct Γ) :
    ProofStruct (Γ.map f) where
  Ξ := P.Ξ.map f
  axs := P.axs.mapEquiv (P.Ξ.mapOccEquiv f)

def CutFreeParaproof.toProofStruct :
    {α : Type u} → {Γ : Sequent Atom α} → CutFreeParaproof Γ → ProofStruct Γ
  | _, _, daimon Γ => ProofStruct.daimon Γ
  | _, _, tensor A B Γ Δ π ρ => π.toProofStruct.tensor ρ.toProofStruct
  | _, _, parr A B Γ π => π.toProofStruct.parr
  | _, _, exch f Γ π => π.toProofStruct.exch f

end MLL
