/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

import Mathlib.Data.Finset.Insert

/-! MLL Formulas -/

namespace MLL

universe u

variable {Atom α β : Type*}

@[grind cases]
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | atomDual : Atom → Formula Atom
  | tensor : Formula Atom → Formula Atom → Formula Atom
  | parr : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq

scoped infix:100 " ⊗ " => Formula.tensor
scoped infix:95 " ⅋ " => Formula.parr

namespace Formula

def dual : Formula Atom → Formula Atom
  | atom x => atomDual x
  | atomDual x => atom x
  | tensor A B => parr A.dual B.dual
  | parr A B => tensor A.dual B.dual

@[simp, grind =]
lemma dual_dual (A : Formula Atom) : A.dual.dual = A := by
  induction A <;> simp_all [dual]

@[mk_iff]
inductive IsPos : Formula Atom → List Bool → Prop
  | nil {A : Formula Atom} : IsPos A []
  | tensorL {A B : Formula Atom} {p : List Bool} : A.IsPos p → (A ⊗ B).IsPos (false :: p)
  | tensorR {A B : Formula Atom} {p : List Bool} : B.IsPos p → (A ⊗ B).IsPos (true :: p)
  | parrL {A B : Formula Atom} {p : List Bool} : A.IsPos p → (A ⅋ B).IsPos (false :: p)
  | parrR {A B : Formula Atom} {p : List Bool} : B.IsPos p → (A ⅋ B).IsPos (true :: p)

def poss : Formula Atom → List (List Bool)
  | atom _ => [[]]
  | atomDual _ => [[]]
  | parr A B => [] :: (A.poss.map (false :: ·) ++ B.poss.map (true :: ·))
  | tensor A B => [] :: (A.poss.map (false :: ·) ++ B.poss.map (true :: ·))

lemma mem_poss_iff_isPos (A : Formula Atom) (p : List Bool) : p ∈ A.poss ↔ A.IsPos p := by
  induction A generalizing p with
  | atom _ => rw [isPos_iff]; simp [poss]
  | atomDual _ => rw [isPos_iff]; simp [poss]
  | tensor A B aih bih =>
    cases p with
    | nil => rw [isPos_iff]; simp [poss]
    | cons b p => rw [isPos_iff]; cases b <;> simp_all [poss]
  | parr A B aih bih =>
    cases p with
    | nil => rw [isPos_iff]; simp [poss]
    | cons b p => rw [isPos_iff]; cases b <;> simp_all [poss]

def getOcc? : Formula Atom → List Bool → Option (Formula Atom)
  | A, [] => A
  | atom _, _ :: _ => none
  | atomDual _, _ :: _ => none
  | tensor A _, false :: p => A.getOcc? p
  | tensor _ B, true :: p => B.getOcc? p
  | parr A _, false :: p => A.getOcc? p
  | parr _ B, true :: p => B.getOcc? p

lemma getOcc?_isSome_iff_isPos (A : Formula Atom) (p : List Bool) :
    (A.getOcc? p).isSome ↔ A.IsPos p := by
  induction A generalizing p with
  | atom _ => rw [isPos_iff]; cases p <;> simp [getOcc?]
  | atomDual _ => rw [isPos_iff]; cases p <;> simp [getOcc?]
  | tensor A B aih bih =>
    cases p with
    | nil => rw [isPos_iff]; simp [getOcc?]
    | cons b p => rw [isPos_iff]; cases b <;> simp_all [getOcc?]
  | parr A B aih bih =>
    cases p with
    | nil => rw [isPos_iff]; simp [getOcc?]
    | cons b p => rw [isPos_iff]; cases b <;> simp_all [getOcc?]

instance : GetElem? (Formula Atom) (List Bool) (Formula Atom) IsPos where
  getElem A p h := (A.getOcc? p).get (getOcc?_isSome_iff_isPos A p |>.mpr h)
  getElem? := getOcc?

instance : LawfulGetElem (Formula Atom) (List Bool) (Formula Atom) IsPos where
  getElem?_def A p _ := by
    split
    case isTrue => simp [getElem, getElem?]
    case isFalse => simp_all [←getOcc?_isSome_iff_isPos, getElem?]

protected inductive PartialTree {Atom : Type u} : Formula Atom → Type u where
  | leaf (A : Formula Atom) : A.PartialTree
  | tensor {A B : Formula Atom} : A.PartialTree → B.PartialTree → (A ⊗ B).PartialTree
  | parr {A B : Formula Atom} : A.PartialTree → B.PartialTree → (A ⅋ B).PartialTree

inductive PartialTree.IsLeaf : {A : Formula Atom} → A.PartialTree → List Bool → Prop
  | nil (A : Formula Atom) : (leaf A).IsLeaf []
  | tensorL {A B : Formula Atom} {U : A.PartialTree} {V : B.PartialTree} {p : List Bool} :
      U.IsLeaf p → (U.tensor V).IsLeaf (false :: p)
  | tensorR {A B : Formula Atom} {U : A.PartialTree} {V : B.PartialTree} {p : List Bool} :
      V.IsLeaf p → (U.tensor V).IsLeaf (true :: p)
  | parrL {A B : Formula Atom} {U : A.PartialTree} {V : B.PartialTree} {p : List Bool} :
      U.IsLeaf p → (U.parr V).IsLeaf (false :: p)
  | parrR {A B : Formula Atom} {U : A.PartialTree} {V : B.PartialTree} {p : List Bool} :
      V.IsLeaf p → (U.parr V).IsLeaf (true :: p)

lemma PartialTree.isPos_of_isLeaf {A : Formula Atom} {U : A.PartialTree} {p : List Bool}
    (h : U.IsLeaf p) : A.IsPos p := by induction h <;> rw [isPos_iff] <;> grind

lemma PartialTree.isLeaf_iff_of_heq {A B : Formula Atom} {U : A.PartialTree} {V : B.PartialTree}
    (h : A = B) (h' : U ≍ V) (p : List Bool) : U.IsLeaf p ↔ V.IsLeaf p := by
  subst B
  obtain ⟨h, rfl⟩ := heq_iff_exists_eq_cast.mp h'
  rfl

def PartialTree.tensorIsLeafEquiv {A B : Formula Atom} (U : A.PartialTree) (V : B.PartialTree) :
    {p // (U.tensor V).IsLeaf p} ≃ {p // U.IsLeaf p} ⊕ {p // V.IsLeaf p} where
  toFun
    | ⟨false :: p, h⟩ => .inl ⟨p, by cases h; assumption⟩
    | ⟨true :: p, h⟩ => .inr ⟨p, by cases h; assumption⟩
  invFun
    | .inl ⟨p, h⟩ => ⟨false :: p, .tensorL h⟩
    | .inr ⟨p, h⟩ => ⟨true :: p, .tensorR h⟩
  left_inv := by intro ⟨p, h⟩; cases h <;> rfl
  right_inv := by rintro (⟨p, h⟩ | ⟨p, h⟩) <;> rfl

def PartialTree.parrIsLeafEquiv {A B : Formula Atom} (U : A.PartialTree) (V : B.PartialTree) :
    {p // (U.parr V).IsLeaf p} ≃ {p // U.IsLeaf p} ⊕ {p // V.IsLeaf p} where
  toFun
    | ⟨false :: p, h⟩ => .inl ⟨p, by cases h; assumption⟩
    | ⟨true :: p, h⟩ => .inr ⟨p, by cases h; assumption⟩
  invFun
    | .inl ⟨p, h⟩ => ⟨false :: p, .parrL h⟩
    | .inr ⟨p, h⟩ => ⟨true :: p, .parrR h⟩
  left_inv := by intro ⟨p, h⟩; cases h <;> rfl
  right_inv := by rintro (⟨p, h⟩ | ⟨p, h⟩) <;> rfl

end Formula

abbrev Sequent (Atom α : Type*) := α → Formula Atom

namespace Sequent

protected def cons (A : Formula Atom) (Γ : Sequent Atom α) : Sequent Atom (Option α) :=
  Option.rec A Γ

protected def map (Γ : Sequent Atom α) (f : β → α) : Sequent Atom β := Γ ∘ f

protected def sum (Γ : Sequent Atom α) (Δ : Sequent Atom β) : Sequent Atom (α ⊕ β) :=
    Sum.rec Γ Δ

lemma map_cons_eq (Γ : Sequent Atom (Option α)) : (Γ.map Option.some).cons (Γ none) = Γ := by
  ext a; cases a <;> rfl

protected abbrev PartialTree (Γ : Sequent Atom α) := ∀ (a : α), (Γ a).PartialTree

namespace PartialTree

structure Occ {Γ : Sequent Atom α} (Ξ : Γ.PartialTree) where
  a : α
  p : List Bool
  h : (Ξ a).IsLeaf p

variable {Γ : Sequent Atom α} {Δ : Sequent Atom β} {A B : Formula Atom}

lemma heq_of_eq {a b : α} (h : a = b) (Ξ : Γ.PartialTree) : Ξ a ≍ Ξ b := by rw [h]

protected def cons (U : A.PartialTree) (Ξ : Γ.PartialTree) :
    (Γ.cons A).PartialTree := Option.rec U Ξ

protected def map (Ξ : Γ.PartialTree) (f : β → α) : (Γ.map f).PartialTree :=
  fun b => Ξ (f b)

protected def sum (Ξ : Γ.PartialTree) (Υ : Δ.PartialTree) : (Γ.sum Δ).PartialTree := Sum.rec Ξ Υ

def consOccEquiv (U : A.PartialTree) (Ξ : Γ.PartialTree) :
    (Ξ.cons U).Occ ≃ Ξ.Occ ⊕ {p // U.IsLeaf p} where
  toFun
    | ⟨none, p, h⟩ => .inr ⟨p, h⟩
    | ⟨some a, p, h⟩ => .inl ⟨a, p, h⟩
  invFun
    | .inr ⟨p, h⟩ => ⟨none, p, h⟩
    | .inl ⟨a, p, h⟩ => ⟨some a, p, h⟩
  left_inv := by rintro ⟨(_ | a), p, h⟩ <;> rfl
  right_inv := by rintro (⟨a, p, h⟩ | ⟨p, h⟩) <;> rfl

def sumOccEquiv (Ξ : Γ.PartialTree) (Υ : Δ.PartialTree) : (Ξ.sum Υ).Occ ≃ Ξ.Occ ⊕ Υ.Occ where
  toFun
    | ⟨.inl a, p, h⟩ => .inl ⟨a, p, h⟩
    | ⟨.inr b, p, h⟩ => .inr ⟨b, p, h⟩
  invFun
    | .inl ⟨a, p, h⟩ => ⟨.inl a, p, h⟩
    | .inr ⟨b, p, h⟩ => ⟨.inr b, p, h⟩
  left_inv := by rintro ⟨(a | b), p, h⟩ <;> rfl
  right_inv := by rintro (⟨a, p, h⟩ | ⟨b, p, h⟩) <;> rfl

def mapOccEquiv (Ξ : Γ.PartialTree) (f : β ≃ α) :
    Ξ.Occ ≃ (Ξ.map f).Occ where
  toFun
    | ⟨a, p, h⟩ => ⟨f.symm a, p, by
      refine Formula.PartialTree.isLeaf_iff_of_heq (by simp [Sequent.map]) ?_ p |>.mp h
      exact PartialTree.heq_of_eq (f.apply_symm_apply a |>.symm) Ξ
    ⟩
  invFun
    | ⟨a, p, h⟩ => ⟨f a, p, by simpa⟩
  left_inv := by intro ⟨a, p, h⟩; simp
  right_inv := by intro ⟨a, p, h⟩; simp

def tensorOccEquiv (U : A.PartialTree) (V : B.PartialTree) (Ξ : Γ.PartialTree) (Υ : Δ.PartialTree) :
    (Ξ.cons U).Occ ⊕ (Υ.cons V).Occ ≃ (Ξ.sum Υ |>.cons (U.tensor V)).Occ :=
  (consOccEquiv U Ξ).sumCongr (consOccEquiv V Υ) |>.trans <|
    (Equiv.sumSumSumComm ..).symm.trans <|
    (sumOccEquiv Ξ Υ).sumCongr (U.tensorIsLeafEquiv V) |>.symm.trans <|
    (consOccEquiv _ _).symm

def parrOccEquiv (U : A.PartialTree) (V : B.PartialTree) (Ξ : Γ.PartialTree) :
    (Ξ.cons U |>.cons V).Occ ≃ (Ξ.cons (U.parr V)).Occ :=
  (consOccEquiv V _).trans <|
    ((consOccEquiv U Ξ).sumCongr (.refl _)).trans <|
    (Equiv.sumAssoc _ _ _).trans <|
    (Equiv.refl Ξ.Occ).sumCongr (U.parrIsLeafEquiv V).symm |>.trans (consOccEquiv ..).symm

def extEquiv {Γ Γ' : Sequent Atom α} (Ξ : Γ.PartialTree) (Ξ' : Γ'.PartialTree)
    (h : ∀ a p, (Ξ a).IsLeaf p ↔ (Ξ' a).IsLeaf p) : Ξ.Occ ≃ Ξ'.Occ where
  toFun
    | ⟨a, p, hp⟩ => ⟨a, p, h a p |>.mp hp⟩
  invFun
    | ⟨a, p, hp⟩ => ⟨a, p, h a p |>.mpr hp⟩

end PartialTree

end Sequent

namespace Formula

inductive Shape : Type where
  | leaf : Shape
  | tensor : Shape → Shape → Shape
  | parr : Shape → Shape → Shape
  deriving DecidableEq

scoped infix:100 " ⊗ " => Formula.Shape.tensor
scoped infix:95 " ⅋ " => Formula.Shape.parr

namespace Shape

@[mk_iff]
inductive IsPos : Shape → List Bool → Prop where
  | nil {s : Shape} : IsPos s []
  | tensorL {s t : Shape} {p : List Bool} : s.IsPos p → (s ⊗ t).IsPos (false :: p)
  | tensorR {s t : Shape} {p : List Bool} : t.IsPos p → (s ⊗ t).IsPos (true :: p)
  | parrL {s t : Shape} {p : List Bool} : s.IsPos p → (s ⅋ t).IsPos (false :: p)
  | parrR {s t : Shape} {p : List Bool} : t.IsPos p → (s ⅋ t).IsPos (true :: p)

attribute [simp] IsPos.nil

@[simp] lemma IsPos.leaf_iff (p : List Bool) : leaf.IsPos p ↔ p = [] := by
  rw [isPos_iff]; simp

def getSub? : Shape → List Bool → Option Shape
  | S, [] => some S
  | leaf, _ :: _ => none
  | tensor s _, false :: p => s.getSub? p
  | tensor _ t, true :: p => t.getSub? p
  | parr s _, false :: p => s.getSub? p
  | parr _ t, true :: p => t.getSub? p

lemma isPos_iff_getSub?_isSome (s : Shape) (p : List Bool) :
    s.IsPos p ↔ (s.getSub? p).isSome := by
  induction s generalizing p with
  | leaf => rw [isPos_iff]; cases p <;> simp [getSub?]
  | tensor s t sih tih =>
    rw [isPos_iff]
    cases p with
    | nil => simp [getSub?]
    | cons b p => cases b <;> simp_all [getSub?]
  | parr s t sih tih =>
    rw [isPos_iff]
    cases p with
    | nil => simp [getSub?]
    | cons b p => cases b <;> simp_all [getSub?]

instance (s : Shape) (p : List Bool) : Decidable (s.IsPos p) :=
  decidable_of_bool (s.getSub? p |>.isSome) (isPos_iff_getSub?_isSome s p).symm

lemma IsPos.getSub?_isSome {s : Shape} {p : List Bool} (h : s.IsPos p) : (s.getSub? p).isSome :=
    isPos_iff_getSub?_isSome s p |>.mp h

instance : GetElem Shape (List Bool) Shape IsPos where
  getElem s p h := s.getSub? p |>.get h.getSub?_isSome

instance : GetElem? Shape (List Bool) Shape IsPos where
  getElem? s p := s.getSub? p

instance : LawfulGetElem Shape (List Bool) Shape IsPos where
  getElem?_def s p _ := by
    split <;> simp [getElem?, getElem]
    grind [Option.not_isSome_iff_eq_none, isPos_iff_getSub?_isSome]

@[mk_iff]
inductive ExtendedBy : Shape → Shape → Prop where
  | leaf (s : Shape) : ExtendedBy leaf s
  | tensor {s s' t t' : Shape} : s.ExtendedBy s' → t.ExtendedBy t' → (s ⊗ t).ExtendedBy (s' ⊗ t')
  | parr {s s' t t' : Shape} : s.ExtendedBy s' → t.ExtendedBy t' → (s ⅋ t).ExtendedBy (s' ⅋ t')

instance : PartialOrder Shape where
  le := ExtendedBy
  le_refl s := by induction s <;> constructor <;> grind
  le_trans := by
    intro _ _ u h h'
    induction h generalizing u with
    | leaf => exact .leaf u
    | tensor => cases h'; constructor <;> grind
    | parr => cases h'; constructor <;> grind
  le_antisymm s t h h' := by induction h <;> cases h' <;> grind

@[simp] lemma leaf_le (s : Shape) : leaf ≤ s := ExtendedBy.leaf s

lemma tensor_le_iff (s₁ s₂ t : Shape) : s₁ ⊗ s₂ ≤ t ↔ ∃ t₁ t₂, s₁ ≤ t₁ ∧ s₂ ≤ t₂ ∧ t = t₁ ⊗ t₂ := by
  simp_rw [LE.le]; rw [extendedBy_iff]; simp

lemma parr_le_iff (s₁ s₂ t : Shape) : s₁ ⅋ s₂ ≤ t ↔ ∃ t₁ t₂, s₁ ≤ t₁ ∧ s₂ ≤ t₂ ∧ t = t₁ ⅋ t₂ := by
  simp_rw [LE.le]; rw [extendedBy_iff]; simp

lemma IsPos.isPos_of_le {s t : Shape} (h : s ≤ t) {p : List Bool} (hs : s.IsPos p) :
    t.IsPos p := by
  induction s generalizing t p with
  | leaf => simp_all [IsPos.leaf_iff]
  | tensor s₁ s₂ ih₁ ih₂ =>
    cases h with
    | tensor h₁ h₂ =>
      cases hs with
      | nil => exact IsPos.nil
      | tensorL hs => exact (ih₁ h₁ hs).tensorL
      | tensorR hs => exact (ih₂ h₂ hs).tensorR
  | parr s₁ s₂ ih₁ ih₂ =>
    cases h with
    | parr h₁ h₂ =>
      cases hs with
      | nil => exact IsPos.nil
      | parrL hs => exact (ih₁ h₁ hs).parrL
      | parrR hs => exact (ih₂ h₂ hs).parrR

@[mk_iff]
inductive IsLeafPos : Shape → List Bool → Prop where
  | leaf : IsLeafPos leaf []
  | tensorL {s t : Shape} {p : List Bool} : s.IsLeafPos p → (s ⊗ t).IsLeafPos (false :: p)
  | tensorR {s t : Shape} {p : List Bool} : t.IsLeafPos p → (s ⊗ t).IsLeafPos (true :: p)
  | parrL {s t : Shape} {p : List Bool} : s.IsLeafPos p → (s ⅋ t).IsLeafPos (false :: p)
  | parrR {s t : Shape} {p : List Bool} : t.IsLeafPos p → (s ⅋ t).IsLeafPos (true :: p)

lemma IsLeafPos.getElem?_eq {s : Shape} {p : List Bool} (h : s.IsLeafPos p) :
    s[p]? = some Shape.leaf := by
  induction h <;> simp_all [getElem?, getSub?]

lemma isLeafPos_iff_getElem?_eq (s : Shape) (p : List Bool) :
    s[p]? = some leaf ↔ s.IsLeafPos p := by
  refine ⟨?_, fun h => h.getElem?_eq⟩
  rw [getElem?_eq_some_iff]
  intro ⟨h, heq⟩
  induction h with
  | nil => simp_all [getElem, getSub?, IsLeafPos.leaf]
  | tensorL h ih =>
    refine IsLeafPos.tensorL <| ih ?_
    simp_all [getElem, getSub?]
  | tensorR h ih =>
    refine IsLeafPos.tensorR <| ih ?_
    simp_all [getElem, getSub?]
  | parrL h ih =>
    refine IsLeafPos.parrL <| ih ?_
    simp_all [getElem, getSub?]
  | parrR h ih =>
    refine IsLeafPos.parrR <| ih ?_
    simp_all [getElem, getSub?]

instance (s : Shape) (p : List Bool) : Decidable (s.IsLeafPos p) :=
  decidable_of_iff (s[p]? = some leaf) (isLeafPos_iff_getElem?_eq s p)

end Shape

end Formula

end MLL
