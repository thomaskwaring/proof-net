import ProofNet.Vorspeil.Locus
import Mathlib.Logic.Function.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.SetNotation

open Function Finset List

inductive Pitchfork where
  | neg : Locus → Finset Locus → Pitchfork
  | pos : Finset Locus → Pitchfork

def Pitchfork.WF : Pitchfork → Prop
  | neg ξ Λ => Pairwise (Locus.Disjoint on fun ζ : Λ => ζ) ∧ ∀ ζ ∈ Λ, ξ.Disjoint ζ
  | pos Λ => Pairwise (Locus.Disjoint on fun ζ : Λ => ζ)

lemma Pitchfork.WF.notMem_of_neg {ξ : Locus} {Λ : Finset Locus} (h : neg ξ Λ |>.WF) : ¬ ξ ∈ Λ :=
  fun hcon => (h.2 _ hcon).2 prefix_rfl

open Locus Pitchfork

inductive FinDessin : Pitchfork → Type where
  | fides {Λ : Finset Locus} (hwf : pos Λ |>.WF) : FinDessin (pos Λ)
  | daimon {Λ : Finset Locus} (hwf : pos Λ |>.WF) : FinDessin (pos Λ)
  | consPos {ξ : Locus} {Λ : Finset Locus} {I : Finset ℕ} {Λ_ : I → Finset Locus}
      (hsub : ∀ i : I, Λ_ i ⊆ Λ) (hdisj : (Set.range Λ_).PairwiseDisjoint id)
      (hwf : neg ξ Λ |>.WF) (ψ_ : (i : I) → FinDessin <| neg (ξ.concat i) (Λ_ i)) :
      FinDessin (pos <| Λ.cons ξ hwf.notMem_of_neg)
  | consNeg {ζ : Locus} {Λ : Finset Locus} {Λ_ : Finset ℕ → Finset Locus}
      (hsub : ∀ J, Λ_ J ⊆ Λ) (hwf : neg ζ Λ |>.WF)
      (φ_ : (J : Finset ℕ) → FinDessin <| pos (ζ.mconcat J ∪ Λ_ J)) : FinDessin (neg ζ Λ)


/-- Pseudo-dessin on a focus of type `Option Locus`, where `none` indicates a positive phase, and
  `some ζ` indicates a negative phase focussed on `ζ`. -/
inductive PDessin : Option Locus → Type where
  | fides : PDessin none
  | daimon : PDessin none
  | consPos (ξ : Locus) (I : Finset ℕ) (ψ_ : (i : I) → PDessin (ξ.concat i)) : PDessin none
  | consNeg (ζ : Locus) (φ_ : Finset ℕ → PDessin none) : PDessin ζ

inductive Action : Type where
  | daimon : Action
  | pos (ξ : Locus) (I : Finset ℕ) : Action
  | neg (ζ : Locus) (J : Finset ℕ) : Action

def PDessin.chronicles {f : Option Locus} : PDessin f → Set (List Action)
  | fides => {}
  | daimon => {[Action.daimon]}
  | consPos ξ I ψ_ => {[]} ∪ {(Action.pos ξ I) :: k | (i : I) (k ∈ (ψ_ i).chronicles)}
  | consNeg ζ φ_ => {(Action.neg ζ J) :: k | (J : Finset ℕ) (k : (φ_ J).chronicles)}

inductive Dessin : {f : Option Locus} → PDessin f → Pitchfork → Type where
  | fid {Λ : Finset Locus} (h : (pos Λ).WF) : Dessin .fides (pos Λ)
  | dai {Λ : Finset Locus} (h : (pos Λ).WF) : Dessin .fides (pos Λ)
  | consPos (ξ : Locus) (I : Finset ℕ) (ψ_ : (i : I) → PDessin (ξ.concat i)) (Λ : Finset Locus)
      (Λ_ : (i : I) → Finset Locus) (hsub : ∀ i : I, Λ_ i ⊆ Λ)
      (hdisj : ∀ (i j : I), i ≠ j → Λ_ i ∩ Λ_ j = ∅) (hwf : (neg ξ Λ).WF)
      (Ψ_ : (i : I) → Dessin (ψ_ i) (neg (ξ.concat i) (Λ_ i))) :
      Dessin (.consPos ξ I ψ_) (pos <| insert ξ Λ)
  | consNeg (ζ : Locus) (φ_ : Finset ℕ → PDessin none) (Λ : Finset Locus)
      (Λ_ : Finset ℕ → Finset Locus) (hsub : ∀ J : Finset ℕ, Λ_ J ⊆ Λ) (hwf : (neg ζ Λ).WF)
      (Φ_ : (J : Finset ℕ) → Dessin (φ_ J) (.pos <| ζ.mconcat J ∪ Λ_ J)) :
      Dessin (.consNeg ζ φ_) (neg ζ Λ)
