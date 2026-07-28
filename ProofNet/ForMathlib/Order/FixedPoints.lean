import Mathlib.Order.FixedPoints

namespace OrderHom

variable {α : Type*} [CompleteLattice α]

lemma map_le_nextFixed (f : α →o α) {x y : α} (hx : x ≤ f x) (hy : y ≤ f.nextFixed x hx) :
    f y ≤ f.nextFixed x hx := le_sup_right.trans (map_le_lfp _ hy)

lemma nextFixed_le_of_map_le (f : α →o α) {x y : α} (h : x ≤ y) (hx : x ≤ f x) (hy : f y ≤ y) :
    f.nextFixed x hx ≤ y := lfp_le _ (sup_le h hy)

lemma prevFixed_le_map (f : α →o α) {x y : α} (hy : f y ≤ y) (hx : f.prevFixed y hy ≤ x) :
    f.prevFixed y hy ≤ f x := (gfp_le_map _ hx).trans inf_le_right

lemma le_prevFixed_of_le_map (f : α →o α) {x y : α} (h : x ≤ y) (hx : x ≤ f x) (hy : f y ≤ y) :
    x ≤ f.prevFixed y hy := le_gfp _ (le_inf h hx)

theorem nextFixed_induction (f : α →o α) {p : α → Prop} {x : α} (hx : x ≤ f x)
    (base : p x) (step : ∀ y, p y → x ≤ y → y ≤ f.nextFixed x hx → p (f y))
    (hSup : ∀ s, (∀ y ∈ s, p y) → p (sSup s)) : p (f.nextFixed x hx) := by
  set s := {y | x ≤ y ∧ y ≤ f.nextFixed x hx ∧ p y}
  specialize hSup s (fun _ ⟨_, _, hy⟩ => hy)
  suffices sSup s = f.nextFixed x hx from this ▸ hSup
  have h : sSup s ≤ f.nextFixed x hx := sSup_le fun y (⟨_, hy, _⟩ : y ∈ s) => hy
  have hxs : x ≤ sSup s := le_sSup ⟨le_rfl, f.le_nextFixed hx, base⟩
  have hmem : f (sSup s) ∈ s :=
    ⟨hx.trans (f.mono hxs), f.map_le_nextFixed hx h, step _ hSup hxs h⟩
  exact h.antisymm (f.nextFixed_le_of_map_le hxs hx <| le_sSup hmem)

theorem nextFixed_le_prevFixed (f : α →o α) {x y : α} (h : x ≤ y) (hx : x ≤ f x) (hy : f y ≤ y) :
  f.nextFixed x hx ≤ f.prevFixed y hy := f.nextFixed_le hx <| f.le_prevFixed_of_le_map h hx hy

lemma nextFixed_mono_base (f : α →o α) {x y : α} (h : x ≤ y) (hx : x ≤ f x) (hy : y ≤ f y) :
    f.nextFixed x hx ≤ f.nextFixed y hy := by
  apply f.nextFixed_induction (p := (· ≤ f.nextFixed y hy))
  · exact h.trans (f.le_nextFixed hy)
  · intro z hz _ _
    convert f.mono hz
    exact (f.nextFixed y hy).property.symm
  · intro s
    exact sSup_le

lemma nextFixed_eq_self (f : α →o α) (x : Function.fixedPoints f) :
    f.nextFixed x x.property.ge = x :=
  (f.nextFixed_le _ le_rfl).antisymm (f.le_nextFixed x.property.ge)

lemma coe_nextFixed_eq_self (f : α →o α) {x : α} (h : f x = x) : f.nextFixed x h.ge = x :=
  (f.nextFixed_le_of_map_le le_rfl h.ge h.le).antisymm (f.le_nextFixed h.ge)

end OrderHom
