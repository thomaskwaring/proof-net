import Mathlib.Combinatorics.Graph.Basic

variable {α β γ : Type*}

open Sum

namespace Graph

structure Bipartite (α β γ : Type*) where
  vertexSetL : Set α
  vertexSetR : Set β
  IsLink : γ → α → β → Prop
  edgeSet : Set γ := {e : γ | ∃ x y, IsLink e x y}
  eq_and_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∧ y = w
  edge_mem_iff_exists_isLink (e : γ) : e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by
    exact fun _ => Iff.rfl
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSetL := by grind
  right_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → y ∈ vertexSetR := by grind

namespace Bipartite

variable {G : Bipartite α β γ}

def toGraph (G : Bipartite α β γ) : Graph (α ⊕ β) γ where
  vertexSet := inl '' G.vertexSetL ∪ inr '' G.vertexSetR
  IsLink e
    | inl x, inr y => G.IsLink e x y
    | inr y, inl x => G.IsLink e x y
    | _, _ => False
  edgeSet := G.edgeSet
  isLink_symm e he x y hxy := by grind
  edge_mem_iff_exists_isLink e := by simp [G.edge_mem_iff_exists_isLink]; grind
  eq_or_eq_of_isLink_of_isLink := by grind [Bipartite.eq_and_eq_of_isLink_of_isLink]
  left_mem_of_isLink := by grind [Bipartite.left_mem_of_isLink, Bipartite.right_mem_of_isLink]

@[simp, grind =]
lemma inl_mem_vertexSet_toGraph {x : α} : inl x ∈ G.toGraph.vertexSet ↔ x ∈ G.vertexSetL := by
  simp [toGraph]

@[simp, grind =]
lemma inr_mem_vertexSet_toGraph {x : β} : inr x ∈ G.toGraph.vertexSet ↔ x ∈ G.vertexSetR := by
  simp [toGraph]

@[simp, grind =]
lemma isLink_inl_inr_toGraph {e x y} : G.toGraph.IsLink e (inl x) (inr y) ↔ G.IsLink e x y := by
  simp [toGraph]

@[simp, grind =]
lemma isLink_inr_inl_toGraph {e x y} : G.toGraph.IsLink e (inr y) (inl x) ↔ G.IsLink e x y := by
  simp [toGraph]

@[grind .]
lemma not_isLink_inl_inl_toGraph {e x x'} : ¬ G.toGraph.IsLink e (inl x) (inl x') := by
  simp [toGraph]

@[grind .]
lemma not_isLink_inr_inr_toGraph {e y y'} : ¬ G.toGraph.IsLink e (inr y) (inr y') := by
  simp [toGraph]

@[simp, grind =]
lemma mem_edgeSet_toGraph_iff {e : γ} : e ∈ G.toGraph.edgeSet ↔ ∃ x y, G.IsLink e x y := by
  simp [toGraph, G.edge_mem_iff_exists_isLink]

end Bipartite

end Graph
