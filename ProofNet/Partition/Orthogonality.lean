import ProofNet.Partition.Basic
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Graph Partition Sum

variable {α : Type*}

def Set.double (s : Set α) : Set (α ⊕ α) := inl '' s ∪ inr '' s

@[simp, grind =]
lemma Set.inl_mem_double_iff {s : Set α} {x : α} : inl x ∈ s.double ↔ x ∈ s := by simp [double]

@[simp, grind =]
lemma Set.inr_mem_double_iff {s : Set α} {x : α} : inr x ∈ s.double ↔ x ∈ s := by simp [double]

lemma Set.mem_double {s : Set α} {x : α} : x ∈ s ↔ (inl x ∈ s.double ∧ inr x ∈ s.double) := by
  simp

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
  symm _ _ h := by rw [memAdj_iff]; grind
  loopless := by constructor; intro _ h; cases h

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
    P.simpleGraph.neighborSet (inl u) = inr '' (inl ⁻¹' u) ∪ inr '' (inr ⁻¹' u) := by
  grind [SimpleGraph.mem_neighborSet, MemAdj.inl_iff]

lemma simpleGraph.neighbourSet_inl_eq_of_notMem {u : Set (α ⊕ α)} (hu : u ∉ P) :
    P.simpleGraph.neighborSet (inl u) = ∅ := by
  ext
  simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  contrapose! hu
  exact hu.inl_mem

end Partition
