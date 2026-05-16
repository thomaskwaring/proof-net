import Mathlib.Order.Partition.Basic

open Order

lemma sSupIndep_iff_pairwise_disjoint {α : Type*} [Frame α] (s : Set α) :
    sSupIndep s ↔ s.PairwiseDisjoint id := by
  refine ⟨fun h => h.pairwiseDisjoint, ?_⟩
  intro h u hu
  rw [disjoint_sSup_iff]
  intro b ⟨hb, hb'⟩
  apply h hu hb <| fun heq => hb' heq.symm

namespace Partition

def ofFrame {α : Type*} [Order.Frame α] {s : α} (parts : Set α) (hindep : parts.PairwiseDisjoint id)
    (hbot : ⊥ ∉ parts) (hsup : sSup parts = s) : Partition s where
  parts := parts
  sSupIndep' := sSupIndep_iff_pairwise_disjoint parts |>.mpr hindep
  bot_notMem' := hbot
  sSup_eq' := hsup

def merge {α : Type*} [Order.Frame α] {s : α} (P : Partition s) {u v : α}
    (hu : u ∈ P) (hv : v ∈ P) : Partition s := by
  refine ofFrame (insert (u ⊔ v) (P \ {u, v})) ?_ ?_ ?_
  · rintro a (rfl | ⟨ha, _⟩) b hb hab
    · simp_rw [Function.onFun, id_eq, ←sSup_pair]
      refine (P.sSupIndep.disjoint_sSup ?_ (Set.pair_subset hu hv) ?_).symm
      all_goals grind
    · rcases hb with (rfl | ⟨hb, hb'⟩)
      · simp_rw [Function.onFun, id_eq, ←sSup_pair]
        refine (P.sSupIndep.disjoint_sSup ?_ (Set.pair_subset hu hv) ?_)
        all_goals grind
      · exact P.disjoint ha hb hab
  · rintro (h | h)
    · rw [eq_comm, sup_eq_bot_iff] at h
      exact P.ne_bot_of_mem hu h.1
    · exact P.bot_notMem h.1
  · rw [le_antisymm_iff, sSup_le_iff]
    constructor
    · rintro b (rfl | hb)
      · exact sup_le (P.le_of_mem hu) (P.le_of_mem hv)
      · exact P.le_of_mem hb.1
    · simp_rw [←P.sSup_eq]
      apply sSup_le_sSup_of_isCofinalFor
      intro w hw
      by_cases hw' : (w ≤ u ⊔ v)
      · exact ⟨u ⊔ v, Set.mem_insert .., hw'⟩
      · refine ⟨w, Set.mem_insert_of_mem _ ⟨hw, ?_⟩, le_rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hw' (h ▸ le_sup_left), fun h => hw' (h ▸ le_sup_right)⟩




end Partition
