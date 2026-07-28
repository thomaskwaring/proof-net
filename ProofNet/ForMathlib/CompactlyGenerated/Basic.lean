import Mathlib.Order.CompactlyGenerated.Basic
import ProofNet.ForMathlib.SupIndep

variable {α : Type*}

lemma IsAtom.isCompactElement [Order.Frame α] {x : α} (h : IsAtom x) : IsCompactElement x := by
  intro s u _ _ hu hx
  rwa [←hu.sSup_eq, IsAtom.le_sSup h] at hx

instance [Order.Frame α] [IsAtomistic α] : IsCompactlyGenerated α where
  exists_sSup_eq x := by
    obtain ⟨s, hx, hs⟩ := isLUB_atoms x
    refine ⟨s, fun a ha => (hs a ha).isCompactElement, hx.sSup_eq⟩

theorem sSupIndep.disjoint_sSup_sSup {α : Type*} [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] {s t u : Set α} (hs : sSupIndep s) (hts : t ⊆ s) (hus : u ⊆ s)
    (hdisj : Disjoint t u) : Disjoint (sSup t) (sSup u) := by
  rw [sSupIndep_iff] at hs
  rw [←biSup_preimage (f := Subtype.val (p := (· ∈ s))),
    ←biSup_preimage (f := Subtype.val (p := (· ∈ s)))]
  · exact hs.disjoint_biSup_biSup (s := Subtype.val ⁻¹' t) (t := Subtype.val ⁻¹' u)
      (hdisj.preimage _)
  · intro x hx; use ⟨x, hus hx⟩; simpa
  · intro x hx; use ⟨x, hts hx⟩; simpa
