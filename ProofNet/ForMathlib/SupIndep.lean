import Mathlib.Order.SupIndep

lemma biSup_preimage {α ι : Type*} [CompleteLattice α] (s : Set α) {f : ι → α}
    (hf : (f ⁻¹' s).SurjOn f s) : ⨆ i ∈ f ⁻¹' s, f i = sSup s := by
  apply le_antisymm
  · simp only [Set.mem_preimage, iSup_le_iff]
    intro; exact le_sSup
  · apply sSup_le
    intro a ha
    obtain ⟨i, hi, rfl⟩ := hf ha
    exact le_biSup f hi

theorem sSupIndep.disjoint_sSup_sSup' {α : Type*} [CompleteLattice α] [IsModularLattice α]
    {s t u : Set α} (hs : sSupIndep s) (hts : t ⊆ s) (hus : u ⊆ s) (ht : t.Finite)
    (hdisj : Disjoint t u) : Disjoint (sSup t) (sSup u) := by
  rw [sSupIndep_iff] at hs
  rw [←biSup_preimage (f := Subtype.val (p := (· ∈ s))),
    ←biSup_preimage (f := Subtype.val (p := (· ∈ s)))]
  · exact hs.disjoint_biSup_biSup' (s := Subtype.val ⁻¹' t) (t := Subtype.val ⁻¹' u)
      (hdisj.preimage _) (ht.preimage Set.injOn_subtype_val)
  · intro x hx; use ⟨x, hus hx⟩; simpa
  · intro x hx; use ⟨x, hts hx⟩; simpa

theorem sSupIndep.union_of_disjoint_sSup_sSup [Order.Frame α] {s t : Set α}
    (hs : sSupIndep s) (ht : sSupIndep t) (h : Disjoint (sSup s) (sSup t)) :
    sSupIndep (s ∪ t) := by
  rintro x (hx | hx)
  · rw [Set.union_diff_distrib, sSup_union]
    exact Disjoint.sup_right (hs hx) <| h.mono (le_sSup hx) (sSup_le_sSup Set.diff_subset)
  · rw [Set.union_diff_distrib, sSup_union]
    exact Disjoint.sup_right (h.symm.mono (le_sSup hx) (sSup_le_sSup Set.diff_subset)) (ht hx)

theorem sSupIndep.sUnion_of_forall_sSupIndep_of_pairwiseDisjoint_sSup [Order.Frame α]
    {S : Set (Set α)} (h : ∀ s ∈ S, sSupIndep s) (h' : S.PairwiseDisjoint sSup) :
    sSupIndep (⋃₀ S) := by
  intro x ⟨s, hs, hx⟩
  rw [disjoint_sSup_iff]
  intro y ⟨⟨t, ht, hy⟩, hxy⟩
  by_cases hy' : y ∈ s
  · apply (h s hs hx).mono_right
    exact le_sSup ⟨hy', hxy⟩
  · have : Disjoint (sSup s) (sSup t) := h' hs ht <| (ne_of_mem_of_not_mem' hy hy').symm
    exact this.mono (le_sSup hx) (le_sSup hy)

theorem sSupIndep.iUnion_of_forall_sSupIndep_of_pairwiseDisjoint_sSup [Order.Frame α] {ι : Type*}
    {S : ι → Set α} (h : ∀ i, sSupIndep (S i))
    (h' : Set.univ.PairwiseDisjoint (sSup ∘ S)) : sSupIndep (⋃ i : ι, S i) := by
  rw [←Set.sUnion_range]
  apply sUnion_of_forall_sSupIndep_of_pairwiseDisjoint_sSup (by simpa)
  grind [Set.PairwiseDisjoint, Set.Pairwise]
