import Mathlib.Order.Partition.Basic
import ProofNet.ForMathlib.PFun

/-!
TODO
- mapping index sets
- bind / combine
- restrict / extend
-/

variable {ι κ α : Type*} {s t : Set α}

open PFun Part

namespace Partition

structure Indexed (ι : Type*) (s : Set α) where
  part : ι → Set α
  eq_of_mem {x : α} {i j : ι} : x ∈ part i → x ∈ part j → i = j
  index : α →. ι
  mem_index_iff {x : α} {i : ι} : i ∈ index x ↔ x ∈ part i
  index_dom : index.Dom = s

attribute [simp] Indexed.index_dom

namespace Indexed

def getIndex (P : Indexed ι s) {x : α} (h : x ∈ s) : ι := P.index.fn x <| by rwa [P.index_dom]

lemma getIndex_mem_index (P : Indexed ι s) {x : α} (h : x ∈ s) : P.getIndex h ∈ P.index x :=
  get_mem ..

lemma mem_part_getIndex (P : Indexed ι s) {x : α} (h : x ∈ s) : x ∈ P.part (P.getIndex h) :=
  P.mem_index_iff.mp <| P.getIndex_mem_index h

lemma getIndex_eq_of_mem {P : Indexed ι s} {x : α} {i : ι} (hx : x ∈ s) (h : i ∈ P.index x) :
    P.getIndex hx = i := Part.get_eq_of_mem h ..

@[simp]
lemma iUnion_part (P : Indexed ι s) : ⋃ i, P.part i = s := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    rw [←P.index_dom, mem_dom]
    use! i, P.mem_index_iff.mpr h
  · intro h
    use! P.part (P.getIndex h), P.getIndex h, P.mem_part_getIndex h

lemma part_subset (P : Indexed ι s) (i : ι) : P.part i ⊆ s := by
  simp_rw [←P.iUnion_part]; exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a_1 ↦ a_1

lemma mem_of_mem_part {P : Indexed ι s} {i : ι} {x : α} (h : x ∈ P.part i) : x ∈ s :=
  P.part_subset i h

lemma part_eq_iff (P Q : Indexed ι s) : P.part = Q.part ↔ P = Q := by
  rcases P with ⟨p, _, _, hp_mem, _⟩; rcases Q with ⟨q, _, _, hq_mem, _⟩
  simp only [mk.injEq, iff_self_and]
  rintro rfl
  ext
  rw [hp_mem, hq_mem]

@[ext]
lemma ext_part {P Q : Indexed ι s} (h : P.part = Q.part) : P = Q := P.part_eq_iff Q |>.mp h

lemma part_apply_eq (P : Indexed ι s) (i : ι) : P.part i = {x | i ∈ P.index x} := by
  ext; simp [P.mem_index_iff]

lemma index_eq_iff (P Q : Indexed ι s) : P.index = Q.index ↔ P = Q := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  ext i x
  simp [←mem_index_iff, h]

def partOf (P : Indexed ι s) (x : α) : Set α := {y | ∃ i ∈ P.index x, y ∈ P.part i}

lemma mem_partOf_iff (P : Indexed ι s) (x y : α) :
  y ∈ P.partOf x ↔ ∃ i, i ∈ P.index x ∧ i ∈ P.index y := by simp [partOf, mem_index_iff]

lemma partOf_eq_of_mem {P : Indexed ι s} {x : α} (h : x ∈ s) :
    P.partOf x = P.part (P.getIndex h) := by
  ext y
  constructor
  · intro ⟨i, hi, hy⟩
    rwa [getIndex_eq_of_mem h hi]
  · intro hy
    use P.getIndex h, P.getIndex_mem_index h

lemma partOf_eq_of_notMem {P : Indexed ι s} {x : α} (h : x ∉ s) : P.partOf x = ∅ := by
  ext y; simp only [Set.mem_empty_iff_false, iff_false]
  intro ⟨i, hi, hy⟩
  apply h
  rw [←P.index_dom, mem_dom]
  exact ⟨i, hi⟩

lemma mem_partOf_self_iff (P : Indexed ι s) {x : α} : x ∈ P.partOf x ↔ x ∈ s := by
  simp_rw [mem_partOf_iff, ←P.index_dom]; simp [-index_dom]

lemma nonempty_partOf_iff {P : Indexed ι s} {x : α} : (P.partOf x).Nonempty ↔ x ∈ s := by
  constructor
  · intro ⟨y, hy⟩
    contrapose hy
    simp [P.partOf_eq_of_notMem hy]
  · intro h
    use x
    exact P.mem_partOf_self_iff.mpr h

def copy (P : Indexed ι s) (h : s = t) : Indexed ι t where
  part := P.part
  eq_of_mem := P.eq_of_mem
  index := P.index
  mem_index_iff := P.mem_index_iff
  index_dom := P.index_dom.trans h

@[simp] lemma part_copy (P : Indexed ι s) (h : s = t) : (P.copy h).part = P.part := rfl

lemma eq_copy_of_eq_cast {P : Indexed ι s} {Q : Indexed ι t} (h : s = t) (h' : h ▸ P = Q) :
    P.copy h = Q := by
  induction h
  ext
  simp_all

def support (P : Indexed ι s) : Set ι := {i | (P.part i).Nonempty}

lemma mem_support_iff {P : Indexed ι s} (i : ι) : i ∈ P.support ↔ (P.part i).Nonempty := Iff.rfl

lemma mem_support_of_mem {P : Indexed ι s} {i : ι} {x : α} (h : x ∈ P.part i) : i ∈ P.support :=
  ⟨x, h⟩

lemma mem_support_of_mem_index {P : Indexed ι s} {i : ι} {x : α} (h : i ∈ P.index x) :
    i ∈ P.support := P.mem_support_of_mem <| P.mem_index_iff.mp h

@[simp]
lemma ran_index_eq_support (P : Indexed ι s) : P.index.ran = P.support := by
  ext
  simp [PFun.ran, support, Set.Nonempty, P.mem_index_iff]

@[simp] lemma preimage_ran (P : Indexed ι s) : P.index.preimage P.support = s := by
  simp [←ran_index_eq_support]

lemma part_injOn_support (P : Indexed ι s) : P.support.InjOn P.part := by
  intro i hi j hj h
  exact P.eq_of_mem hi.some_mem (h ▸ hi.some_mem)

lemma pairwiseDisjoint_part (P : Indexed ι s) : Set.univ.PairwiseDisjoint P.part := by
  intro i hi j hj hne
  contrapose! hne
  obtain ⟨x, hp, hq⟩ := Set.not_disjoint_iff.mp hne
  exact P.eq_of_mem hp hq

def meet (P : Indexed ι s) (Q : Indexed κ s) : Indexed (ι × κ) s where
  part p := P.part p.1 ∩ Q.part p.2
  eq_of_mem := by
    intro x ⟨i, j⟩ ⟨i', j'⟩ ⟨hi, hj⟩ ⟨hi', hj'⟩
    ext
    · exact P.eq_of_mem hi hi'
    · exact Q.eq_of_mem hj hj'
  index := P.index.prodLift Q.index
  mem_index_iff := by
    intro x ⟨i, j⟩
    simp [←P.mem_index_iff, ←Q.mem_index_iff, Part.mem_eq]
    grind
  index_dom := by rw [dom_prodLift', P.index_dom, Q.index_dom, s.inter_self]

@[simp] lemma part_meet_apply {P : Indexed ι s} {Q : Indexed κ s} {i : ι} {j : κ} :
    (P.meet Q).part (i, j) = P.part i ∩ Q.part j := rfl

@[simp] lemma getIndex_meet {P : Indexed ι s} {Q : Indexed κ s} {x : α} (h : x ∈ s) :
  (P.meet Q).getIndex h = (P.getIndex h, Q.getIndex h) := rfl

@[simp] lemma partOf_meet {P : Indexed ι s} {Q : Indexed κ s} {x : α} :
    (P.meet Q).partOf x = P.partOf x ∩ Q.partOf x := by
  by_cases h : x ∈ s
  · simp [P.partOf_eq_of_mem h, Q.partOf_eq_of_mem h, (P.meet Q).partOf_eq_of_mem h]
  · simp [P.partOf_eq_of_notMem h, (P.meet Q).partOf_eq_of_notMem h]

def toPartition (P : Indexed ι s) : Partition s :=
  removeBot (Set.range P.part) (by
    rw [sSupIndep_iff_pairwiseDisjoint, Set.pairwiseDisjoint_range_iff]
    grind [P.eq_of_mem]
  ) (by simp)

lemma toPartition_coe (P : Indexed ι s) :
  (P.toPartition : Set (Set α)) = Set.range P.part \ {∅} := rfl

lemma toPartition_partOf (P : Indexed ι s) : P.toPartition.partOf = P.partOf := by
  ext x y
  simp only [partOf, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨_, ⟨⟨i, rfl⟩, ht⟩, hx, hy⟩ := h.exists
    use i
    simp [P.mem_index_iff, hx, hy]
  · intro ⟨i, hx, hy⟩
    rw [P.mem_index_iff] at hx
    refine ⟨P.part i, ⟨⟨i, rfl⟩, ?_⟩, hx, hy⟩
    simp; grind

def _root_.Partition.toIndexed (P : Partition s) : Partition.Indexed P s where
  part s := s
  eq_of_mem := by simp; grind [P.eq_of_mem_of_mem]
  index x := ⟨x ∈ s, fun h => ⟨P.partOf x, P.partOf_mem h⟩⟩
  mem_index_iff := by
    intro x ⟨t, h⟩
    simp only [mem_mk_iff, Subtype.mk.injEq, exists_prop]
    constructor
    · rintro ⟨h', rfl⟩; exact mem_partOf h'
    · intro h'; exact ⟨P.subset_of_mem h h', P.eq_partOf_of_mem h h' |>.symm⟩
  index_dom := rfl

lemma _root_.Partition.toPartition_toIndexed (P : Partition s) : P.toIndexed.toPartition = P := by
  ext
  simp only [toPartition, toIndexed, Subtype.range_coe_subtype, SetLike.setOf_mem_eq, mem_removeBot,
    SetLike.mem_coe, Set.bot_eq_empty, ne_eq, and_iff_left_iff_imp]
  exact P.ne_bot_of_mem

def _root_.Partition.toIndexed' (P : Partition s) : Partition.Indexed (Set α) s where
  part s := {x | x ∈ s ∧ s ∈ P}
  eq_of_mem := by
    intro x t u ⟨hxt, ht⟩ ⟨hxu, hu⟩
    exact P.eq_of_mem_of_mem ht hu hxt hxu
  index := PFun.res P.partOf s
  mem_index_iff := by
    intro x t
    simp only [mem_res, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, rfl⟩
      exact P.mem_iff_mem_partOf_mem.mp hx
    · intro ⟨hx, ht⟩
      exact ⟨P.subset_of_mem ht hx, P.eq_partOf_of_mem ht hx |>.symm⟩
  index_dom := rfl

lemma _root_.Partition.toPartition_toIndexed' (P : Partition s) : P.toIndexed'.toPartition = P := by
  ext t
  simp only [toPartition, toIndexed', mem_removeBot, Set.mem_range, Set.bot_eq_empty]
  constructor
  · rintro ⟨⟨u, rfl⟩, ht⟩
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr ht
    simp_all
  · intro ht
    refine ⟨⟨t, ?_⟩, P.ne_bot_of_mem ht⟩
    simp [ht]

def merge (P : Indexed ι s) (Q : Indexed κ P.support) : Indexed κ s where
  part j := ⋃ i ∈ Q.part j, P.part i
  eq_of_mem := by
    rintro x j j' ⟨_, ⟨i, rfl⟩, _, ⟨hi, rfl⟩, hxi⟩ ⟨_, ⟨i', rfl⟩, _, ⟨hi', rfl⟩, hxi'⟩
    obtain rfl : i = i' := P.eq_of_mem hxi hxi'
    exact Q.eq_of_mem hi hi'
  index := Q.index.comp P.index
  mem_index_iff := by simp [P.mem_index_iff, Q.mem_index_iff]; grind
  index_dom := by simp

lemma partOf_merge (P : Indexed ι s) (Q : Indexed κ P.support) (x : α) :
    (P.merge Q).partOf x = ⋃ i ∈ P.index x, ⋃ i' ∈ Q.partOf i, P.part i' := by
  ext y
  simp [merge, mem_partOf_iff, P.mem_index_iff, Q.mem_index_iff]
  grind

-- def split (P : Indexed ι s) (Q : (i : ι) → Indexed κ (P.part i)) :
--     Indexed (ι × κ) s where
--   part p := (Q p.fst).part p.snd
--   eq_of_mem := by
--     intro x ⟨i, j⟩ ⟨i', j'⟩ hx hx'
--     have hi := P.eq_of_mem ((Q i).mem_of_mem_part hx) ((Q i').mem_of_mem_part hx')
--     have hPi : P.part i = P.part i' := by congr
--     have hQi : (Q i).copy hPi = Q i' := by apply eq_copy_of_eq_cast hPi; grind
--     simp only [← hQi, part_copy] at hx'
--     simp only [hi, Prod.mk.injEq, true_and]
--     exact (Q i).eq_of_mem hx hx'
--   index

def indiscrete (s : Set α) : Indexed Unit s where
  part _ := s
  eq_of_mem := by simp
  index := res default s
  mem_index_iff := by simp [res]
  index_dom := by simp

def discrete (s : Set α) : Indexed α s where
  part x := {x} ∩ s
  eq_of_mem := by simp
  index := res id s
  mem_index_iff := by simp [res]; grind
  index_dom := by simp

end Indexed

end Partition
