import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

variable {α β γ : Type*}

namespace Graph

def IsSimple (G : Graph α β) : Prop := ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f

def IsLoopless (G : Graph α β) : Prop := ∀ ⦃e x y⦄, G.IsLink e x y → x ≠ y

def toSimpleGraph (G : Graph α β) : SimpleGraph α where
  Adj x y := x ≠ y ∧ ∃ e, G.IsLink e x y
  symm x y := by
    intro ⟨h, e, he⟩
    exact ⟨h.symm, e, G.isLink_comm.mp he⟩

def IsAcyclic (G : Graph α β) : Prop := G.IsSimple ∧ G.IsLoopless ∧ G.toSimpleGraph.IsAcyclic

end Graph
