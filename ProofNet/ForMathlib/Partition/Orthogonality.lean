import ProofNet.ForMathlib.Partition.Basic
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Unique

open Graph Partition Sum Set

variable {α : Type*}

namespace Set

def double (s : Set α) : Set (α ⊕ α) := inl '' s ∪ inr '' s

@[simp, grind =]
lemma inl_mem_double_iff {s : Set α} {x : α} : inl x ∈ s.double ↔ x ∈ s := by simp [double]

lemma inl_mem_double {s : Set α} {x : α} (h : x ∈ s) : inl x ∈ s.double :=
  s.inl_mem_double_iff.mpr h

@[simp, grind =]
lemma inr_mem_double_iff {s : Set α} {x : α} : inr x ∈ s.double ↔ x ∈ s := by simp [double]

lemma inr_mem_double {s : Set α} {x : α} (h : x ∈ s) : inr x ∈ s.double :=
  s.inr_mem_double_iff.mpr h

lemma mem_double {s : Set α} {x : α} : x ∈ s ↔ (inl x ∈ s.double ∧ inr x ∈ s.double) := by grind

@[simp, grind =] lemma double_empty : (∅ : Set α).double = ∅ := by grind

@[simp, grind =] lemma double_union {s t : Set α} : (s ∪ t).double = s.double ∪ t.double := by
  grind

@[simp, grind =] lemma double_singleton {x : α} : ({x} : Set α).double = {inl x, inr x} := by
  grind

@[simp, grind =] lemma double_insert {s : Set α} {x : α} :
  (insert x s).double = s.double ∪ {inl x, inr x} := by grind

@[simp, grind =] lemma double_preimage_inl {s : Set α} : inl ⁻¹' s.double = s := by ext; simp

@[simp, grind =] lemma double_preimage_inr {s : Set α} : inr ⁻¹' s.double = s := by ext; simp

def IsSymm (s : Set (α ⊕ α)) : Prop := ∀ x : α, inl x ∈ s ↔ inr x ∈ s

lemma isSymm_empty : IsSymm (∅ : Set (α ⊕ α)) := by intro x; simp

@[grind .] lemma isSymm_double (s : Set α) : s.double.IsSymm := by intro x; simp

lemma IsSymm.double_preimage_inl {s : Set (α ⊕ α)} (hs : s.IsSymm) : (inl ⁻¹' s).double = s := by
  ext; grind [IsSymm]

lemma IsSymm.double_preimage_inr {s : Set (α ⊕ α)} (hs : s.IsSymm) : (inr ⁻¹' s).double = s := by
  ext; grind [IsSymm]

lemma isSymm_iff_eq_double {s : Set (α ⊕ α)} : s.IsSymm ↔ ∃ (t : Set α), t.double = s :=
  ⟨fun h => ⟨_, h.double_preimage_inl⟩, fun ⟨t, h⟩ => h ▸ isSymm_double t⟩

end Set

def Partition.graph {s : Set α} (P : Partition s.double) : Graph (Set (α ⊕ α)) α where
  vertexSet := P
  edgeSet := s
  IsLink x a b := a ∈ P ∧ b ∈ P ∧ ((inl x ∈ a ∧ inr x ∈ b) ∨ (inr x ∈ a ∧ inl x ∈ b))
  isLink_symm e _ a b := by grind
  eq_or_eq_of_isLink_of_isLink e a b a' b' := by grind [Partition.eq_of_mem_of_mem]
  edge_mem_iff_exists_isLink e := by
    simp_rw [s.mem_double, P.mem_iff_exists]
    grind
  left_mem_of_isLink e x y h := by simp_all

namespace Partition

instance : Unique (Partition (∅ : Set α)) := inferInstanceAs (Unique (Partition (⊥ : Set α)))

section Graphish

section Loops

variable {s : Set (α ⊕ α)} {P : Partition s}

def HasLoopAt (P : Partition s) (x : α) : Prop := P.Rel (inl x) (inr x)

lemma HasLoopAt.inl_mem {x : α} (h : P.HasLoopAt x) : inl x ∈ s := h.left_mem

lemma HasLoopAt.inr_mem {x : α} (h : P.HasLoopAt x) : inr x ∈ s := h.right_mem

def Loopless {s : Set α} (P : Partition s.double) : Prop := ∀ x, ¬ P.HasLoopAt x

end Loops

variable {s : Set α} (P : Partition s.double)

@[mk_iff, grind cases]
inductive MemAdj : Set (α ⊕ α) ⊕ α → Set (α ⊕ α) ⊕ α → Prop where
  | inl_l_mem_r {x : α} {u : Set (α ⊕ α)} (hu : u ∈ P) (h : inl x ∈ u) : MemAdj (inr x) (inl u)
  | inl_r_mem_l {x : α} {u : Set (α ⊕ α)} (hu : u ∈ P) (h : inl x ∈ u) : MemAdj (inl u) (inr x)
  | inr_l_mem_r {x : α} {u : Set (α ⊕ α)} (hu : u ∈ P) (h : inr x ∈ u) : MemAdj (inr x) (inl u)
  | inr_r_mem_l {x : α} {u : Set (α ⊕ α)} (hu : u ∈ P) (h : inr x ∈ u) : MemAdj (inl u) (inr x)

@[reducible]
def simpleGraph {s : Set α} (P : Partition s.double) : SimpleGraph (Set (α ⊕ α) ⊕ α) where
  Adj := P.MemAdj
  symm _ _ h := by grind [MemAdj]
  loopless := by grind [Std.Irrefl]

variable {s : Set α} (P : Partition s.double)

lemma MemAdj.inr_iff (x : α) (a : Set (α ⊕ α) ⊕ α) :
    P.MemAdj (inr x) a ↔ ∃ u ∈ P, (inl x ∈ u ∨ inr x ∈ u) ∧ a = inl u := by
  constructor
  · intro h
    cases h <;> grind
  · rintro ⟨u, hu, (h | h), rfl⟩
    · exact MemAdj.inl_l_mem_r hu h
    · exact MemAdj.inr_l_mem_r hu h

lemma MemAdj.inl_iff (u : Set (α ⊕ α)) (a : Set (α ⊕ α) ⊕ α) :
    P.MemAdj (inl u) a ↔ u ∈ P ∧ ∃ x, (inl x ∈ u ∨ inr x ∈ u) ∧ a = inr x := by
  constructor
  · intro h
    cases h <;> grind
  · rintro ⟨hu, x, (h | h), rfl⟩
    · exact MemAdj.inl_r_mem_l hu h
    · exact MemAdj.inr_r_mem_l hu h

lemma MemAdj.inr_mem {x : α} {a : Set (α ⊕ α) ⊕ α} (h : P.MemAdj (inr x) a) : x ∈ s := by
  rw [MemAdj.inr_iff] at h
  obtain ⟨u, hu, (h | h), rfl⟩ := h
    <;> grind [P.subset_of_mem hu]

lemma MemAdj.inl_mem {u : Set (α ⊕ α)} {a : Set (α ⊕ α) ⊕ α} (h : P.MemAdj (inl u) a) : u ∈ P := by
  cases h <;> assumption

lemma simpleGraph.neighborSet_inr_eq_of_mem {x : α} (hx : x ∈ s) :
    P.simpleGraph.neighborSet (inr x) = {inl (P.partOf (inl x)), inl (P.partOf (inr x))} := by
  ext a
  simp only [SimpleGraph.mem_neighborSet, MemAdj.inr_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · grind [eq_partOf_of_mem]
  · rintro (rfl | rfl)
    · use P.partOf (inl x)
      grind [mem_partOf, partOf_mem]
    · use P.partOf (inr x)
      grind [mem_partOf, partOf_mem]

lemma simpleGraph.neighborSet_empty_of_notMem {x : α} (hx : x ∉ s) :
    P.simpleGraph.neighborSet (inr x) = ∅ := by
  ext a
  simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  contrapose! hx
  exact hx.inr_mem

lemma simpleGraph.neighborSet_inl_eq_of_mem {u : Set (α ⊕ α)} (hu : u ∈ P) :
    P.simpleGraph.neighborSet (inl u) = inr '' (inl ⁻¹' u ∪ inr ⁻¹' u) := by
  grind [SimpleGraph.mem_neighborSet, MemAdj.inl_iff]

lemma simpleGraph.neighbourSet_inl_eq_of_notMem {u : Set (α ⊕ α)} (hu : u ∉ P) :
    P.simpleGraph.neighborSet (inl u) = ∅ := by
  ext
  simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  contrapose! hu
  exact hu.inl_mem

def Indep' {s : Set α} (P : Partition s.double) : Prop := P.simpleGraph.IsTree

end Graphish

section Inductive

def cut {s : Set α} (P : Partition s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    Partition (s \ {x, y}) :=
  P.merge (P.partOf_mem hx) (P.partOf_mem hy) |>.restrict diff_subset

lemma cut_pair {x y : α} (P : Partition {x, y}) :
    P.cut (x := x) (y := y) (by grind) (by grind) = ⊥ := by
  apply Partition.copy_injective diff_self
  subsingleton

-- this validates the mix rule
protected inductive Indep : {s : Set (α ⊕ α)} → Partition s → Prop where
  | empty : Partition.Indep (⊥ : Partition ∅)
  | cut {s : Set (α ⊕ α)} {x : α} {P : Partition s} (hxs : inl x ∈ s) (hxs' : inr x ∈ s)
      (h : P.partOf (inl x) ≠ P.partOf (inr x)) (hcut : (P.cut hxs hxs').Indep) : P.Indep

lemma Indep.isSymm {s : Set (α ⊕ α)} {P : Partition s} (h : P.Indep) : s.IsSymm := by
  induction h with
  | empty => exact isSymm_empty
  | cut => grind [Set.IsSymm]

lemma Indep.copy {s t : Set (α ⊕ α)} (h : s = t) {P : Partition s} (hP : P.Indep) :
    (P.copy h).Indep := by subst t; rwa [copy_refl]

lemma Indep.of_copy {s t : Set (α ⊕ α)} (h : s = t) {P : Partition s} (hP : P.copy h |>.Indep) :
    P.Indep := by subst t; rwa [copy_refl] at hP

lemma Indep.empty' (P : Partition (∅ : Set (α ⊕ α))) : P.Indep := by
  convert Indep.empty
  subsingleton

lemma indep_pair_bot (x : α) : (⊥ : Partition ({inl x, inr x} : Set (α ⊕ α))).Indep := by
  refine Indep.cut (x := x) (by grind) (by grind) ?_ (Indep.of_copy diff_self (Indep.empty' _))
  apply (injOn_partOf_bot {inl x, inr x}).ne <;> simp

end Inductive

end Partition
