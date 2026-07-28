import Mathlib.Data.PFun

namespace PFun

variable {α β γ : Type*}

lemma fn_mem_ran {f : α →. β} {x : α} (h : x ∈ f.Dom) : f.fn x h ∈ f.ran := by
  simp only [ran, fn_apply, Set.mem_setOf_eq]
  use x, h

@[simp] lemma preimage_ran (f : α →. β) : f.preimage f.ran = f.Dom := by
  ext x; rw [mem_preimage, mem_dom]
  exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, ⟨x, hy⟩, hy⟩⟩

lemma dom_prodLift' (f : α →. β) (g : α →. γ) : (f.prodLift g).Dom = f.Dom ∩ g.Dom := by
  ext; simp [Part.mem_eq]

@[simp] lemma dom_restrict (f : α →. β) {s : Set α} (h : s ⊆ f.Dom) :
    (restrict f h).Dom = s := by
  ext
  simp only [mem_dom, mem_restrict, exists_and_left, and_iff_left_iff_imp]
  exact fun hx => f.mem_dom _ |>.mp (h hx)

@[simp] lemma dom_res (f : α → β) (s : Set α) : (res f s).Dom = s := by simp [res]

end PFun
