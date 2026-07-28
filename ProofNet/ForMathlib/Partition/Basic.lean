import Mathlib.Order.Partition.Basic
import Mathlib.Order.Atoms
import ProofNet.ForMathlib.CompactlyGenerated.Basic

open Order Set

namespace Partition

variable {α : Type*}

@[simp] lemma copy_refl [CompleteLattice α] {u : α} (P : Partition u) :
  P.copy (rfl : u = u) = P := rfl

@[simp] lemma copy_trans [CompleteLattice α] {u v w : α} (h : u = v) (h' : v = w)
  (P : Partition u) : (P.copy h).copy h' = P.copy (h.trans h') := rfl

lemma copy_injective [CompleteLattice α] {u v : α} {P Q : Partition u} (h : u = v)
    (h' : P.copy h = Q.copy h) : P = Q := by
  ext
  simp_rw [←mem_copy_iff h, h']

def ofFrame [Order.Frame α] {s : α} (parts : Set α) (hindep : parts.PairwiseDisjoint id)
    (hbot : ⊥ ∉ parts) (hsup : sSup parts = s) : Partition s where
  parts := parts
  sSupIndep' := sSupIndep_iff_pairwiseDisjoint |>.mpr hindep
  bot_notMem' := hbot
  sSup_eq' := hsup

def merge [Order.Frame α] {s : α} (P : Partition s) {u v : α}
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
    · grind [P.bot_notMem]
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

def discrete [Order.Frame α] [IsAtomistic α] (u : α) : Partition u where
  parts := {a | IsAtom a ∧ a ≤ u}
  sSupIndep' := by
    rw [sSupIndep_iff_pairwiseDisjoint]
    intro a ⟨ha, _⟩ b ⟨hb, _⟩
    exact ha.disjoint_of_ne hb
  bot_notMem' := by intro ⟨h, _⟩; exact false_of_ne h.ne_bot
  sSup_eq' := sSup_atoms_le_eq u

instance [Order.Frame α] [IsAtomistic α] (u : α) : OrderBot (Partition u) where
  bot := discrete u
  bot_le P := by
    intro a ⟨ha, hau⟩
    exact ha.le_sSup (s := P.parts) |>.mp (P.sSup_eq'.symm ▸ hau)

lemma coe_bot [Order.Frame α] [IsAtomistic α] (u : α) :
    ((⊥ : Partition u) : Set α) = {a | IsAtom a ∧ a ≤ u} := rfl

lemma mem_bot_iff [Order.Frame α] [IsAtomistic α] (u : α) (a : α) :
    a ∈ (⊥ : Partition u) ↔ IsAtom a ∧ a ≤ u := Iff.rfl

lemma coe_bot_set (s : Set α) : ((⊥ : Partition s) : Set (Set α)) = {{x} | x ∈ s} := by
  simp [coe_bot, Set.isAtom_iff]; grind

lemma mem_bot_set (s t : Set α) : t ∈ (⊥ : Partition s) ↔ ∃ x ∈ s, t = {x} := by
  rw [mem_bot_iff]; simp [Set.isAtom_iff]; grind

lemma partOf_bot_of_mem {s : Set α} {x : α} (h : x ∈ s) : (⊥ : Partition s).partOf x = {x} := by
  refine eq_partOf_of_mem ?_ (mem_singleton _) |>.symm
  simpa [mem_bot_set]

lemma injOn_partOf_bot (s : Set α) : s.InjOn (⊥ : Partition s).partOf := by
  intro x hx y hy
  simp [partOf_bot_of_mem hx, partOf_bot_of_mem hy]

def sup_of_disjoint [Order.Frame α] {u v : α} (P : Partition u) (Q : Partition v)
    (h : Disjoint u v) : Partition (u ⊔ v) where
  parts := P.parts ∪ Q.parts
  sSupIndep' := P.sSupIndep'.union_of_disjoint_sSup_sSup Q.sSupIndep' <| by
    rwa [P.sSup_eq', Q.sSup_eq']
  bot_notMem' := (Or.elim · P.bot_notMem' Q.bot_notMem')
  sSup_eq' := by rw [sSup_union, P.sSup_eq', Q.sSup_eq']

def iSup_of_disjoint [Order.Frame α] {ι : Type*} {u : ι → α} {v : α} (P : (i : ι) → Partition (u i))
    (h : Set.univ.PairwiseDisjoint u) (hv : ⨆ i : ι, u i = v) : Partition v where
  parts := ⋃ i : ι, (P i).parts
  sSupIndep' := sSupIndep.iUnion_of_forall_sSupIndep_of_pairwiseDisjoint_sSup
    (fun i => (P i).sSupIndep') <| by
      intro i _ j _ hne
      simp only [Function.onFun, coe_parts, Function.comp_apply, sSup_eq]
      apply h <;> grind
  bot_notMem' := by rintro ⟨_, ⟨i, rfl⟩, hbot⟩; exact (P i).bot_notMem' hbot
  sSup_eq' := by simp [sSup_iUnion, hv]

def bind [Order.Frame α] {u : α} (P : Partition u) (Q : (v : P.parts) → Partition (v : α)) :
    Partition u := by
  refine iSup_of_disjoint Q ?_ ?_
  · intro ⟨v, hv⟩ _ ⟨w, hw⟩ _ h
    exact P.sSupIndep.pairwiseDisjoint hv hw (by simpa using h)
  · simp [←sSup_range]

lemma coe_bind [Order.Frame α] {u : α} (P : Partition u) (Q : (v : P.parts) → Partition (v : α)) :
    (P.bind Q : Set α) = ⋃ v : (P : Set α), Q v := rfl

lemma mem_bind [Order.Frame α] {u : α} (P : Partition u) (Q : (v : P.parts) → Partition (v : α))
    (a : α) : a ∈ P.bind Q ↔ ∃ v : (P : Set α), a ∈ Q v := by
  rw [←SetLike.mem_coe, coe_bind]; simp

lemma bind_le [Order.Frame α] {u : α} (P : Partition u) (Q : (v : P.parts) → Partition (v : α)) :
    P.bind Q ≤ P := by
  intro a ha
  obtain ⟨⟨v, hv⟩, ha⟩ := mem_bind P Q a |>.mp ha
  use v, hv, (Q ⟨v, hv⟩).le_of_mem ha

def combine [Order.Frame α] [IsCompactlyGenerated α] {u : α} (P : Partition u)
    (Q : Partition (P : Set α)) : Partition u where
  parts := sSup '' Q
  sSupIndep' := by
    rw [sSupIndep_iff_pairwiseDisjoint]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ h
    apply P.sSupIndep.disjoint_sSup_sSup (Q.subset_of_mem hs) (Q.subset_of_mem ht)
    apply Q.sSupIndep.pairwiseDisjoint hs ht
    grind
  bot_notMem' := by
    intro ⟨s, hs, h⟩
    obtain rfl := eq_singleton_bot_of_sSup_eq_bot_of_nonempty h (Q.nonempty_of_mem hs)
    exact P.bot_notMem <| Q.subset_of_mem hs <| mem_singleton ⊥
  sSup_eq' := by
    apply le_antisymm
    · simp only [sSup_le_iff, mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro s hs a ha
      exact P.le_of_mem <| Q.subset_of_mem hs ha
    · simp_rw [←P.sSup_eq, sSup_le_iff]
      intro b hb
      apply le_sSup_of_le (b := sSup <| Q.partOf b)
      · exact ⟨Q.partOf b, Q.partOf_mem hb, rfl⟩
      · exact le_sSup (Q.mem_partOf hb)

lemma coe_combine [Order.Frame α] [IsCompactlyGenerated α] {u : α} (P : Partition u)
    (Q : Partition (P : Set α)) : (P.combine Q : Set α) = sSup '' Q := rfl

lemma mem_combine [Order.Frame α] [IsCompactlyGenerated α] {u : α} (P : Partition u)
    (Q : Partition (P : Set α)) (a : α) : a ∈ P.combine Q ↔ ∃ s ∈ Q, sSup s = a := Iff.rfl

lemma le_combine [Order.Frame α] [IsCompactlyGenerated α] {u : α} (P : Partition u)
    (Q : Partition (P : Set α)) : P ≤ P.combine Q := by
  intro a ha
  use sSup (Q.partOf a)
  constructor
  · use Q.partOf a, Q.partOf_mem ha
  · exact le_sSup (Q.mem_partOf ha)

def restrict' [Order.Frame α] {u : α} (P : Partition u) (v : α) : Partition (u ⊓ v) :=
  removeBot ((· ⊓ v) '' P) (by
    rw [sSupIndep_iff_pairwiseDisjoint]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    apply Disjoint.inf_left; apply Disjoint.inf_right
    exact P.pairwiseDisjoint ha hb (by grind)
  )
  (by simp_rw [sSup_image, ←P.sSup_eq]; exact sSup_inf_eq.symm)

lemma coe_restrict' [Order.Frame α] {u : α} (P : Partition u) (v : α) :
    (P.restrict' v : Set α) = {a ⊓ v | a ∈ P} \ {⊥} := rfl

lemma mem_restrict' [Order.Frame α] {u : α} (P : Partition u) (v a : α) :
    a ∈ P.restrict' v ↔ (∃ a' ∈ P, a' ⊓ v = a) ∧ a ≠ ⊥ := Iff.rfl

lemma inf_mem_restrict' [Order.Frame α] {u a : α} (P : Partition u) (v : α) (ha : a ∈ P) :
  a ⊓ v ∈ P.restrict' v ↔ ¬ Disjoint a v := by grind [disjoint_iff_inf_le, mem_restrict']

def restrict [Order.Frame α] {u v : α} (P : Partition u) (h : v ≤ u) : Partition v :=
  (P.restrict' v).copy (inf_eq_right.mpr h)

lemma coe_restrict [Order.Frame α] {u v : α} (P : Partition u) (h : v ≤ u) :
    (P.restrict h : Set α) = {a ⊓ v | a ∈ P} \ {⊥} := rfl

lemma mem_restrict [Order.Frame α] {u v : α} (P : Partition u) (h : v ≤ u) (a : α) :
    a ∈ P.restrict h ↔ (∃ a' ∈ P, a' ⊓ v = a) ∧ a ≠ ⊥ := Iff.rfl

lemma inf_mem_restrict [Order.Frame α] {u v a : α} (P : Partition u) (h : v ≤ u) (ha : a ∈ P) :
  a ⊓ v ∈ P.restrict h ↔ ¬ Disjoint a v := by grind [disjoint_iff_inf_le, mem_restrict]

end Partition
