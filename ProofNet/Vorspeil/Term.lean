import Mathlib.Algebra.Order.BigOperators.Group.Finset

inductive Term (S : Type*) (ar : S → ℕ) (X : Type*) where
  | var (x : X) : Term S ar X
  | con (c : S) (ts : Fin (ar c) → Term S ar X) : Term S ar X

namespace Term

-- Todo lazy universes
variable {S S' X X' Y Y' Z : Type u} {ar : S → ℕ} {ar' : S' → ℕ}

lemma con_congr {c c' : S} {ts : Fin (ar c) → Term S ar X} {ts' : Fin (ar c') → Term S ar X}
    (heq : con c ts = con c' ts') {i : ℕ} (hi : i < ar c) (hi' : i < ar c') :
    ts ⟨i, hi⟩ = ts' ⟨i, hi'⟩ := by
  obtain ⟨rfl, heq⟩ : c = c' ∧ ts ≍ ts' :=  con.injEq .. ▸ heq
  grind

def size : Term S ar X → ℕ
  | var _ => 1
  | con _ ts => ∑ i, (ts i).size + 1

@[simp] lemma size_var (x : X) : (var (ar := ar) x).size = 1 := rfl

@[simp] lemma size_con {c : S} (ts : Fin (ar c) → Term S ar X) :
  (con c ts).size = ∑ i, (ts i).size + 1 := rfl

lemma size_lt {c : S} (ts : Fin (ar c) → Term S ar X) (i : Fin (ar c)) :
    (ts i).size < (con c ts).size := by
  rw [size_con, Nat.lt_add_one_iff]
  apply Finset.single_le_sum_of_canonicallyOrdered (Finset.mem_univ i)

@[reducible] def getName : Term S ar X → S ⊕ X
  | var x => .inr x
  | con c _ => .inl c

lemma getName_isLeft_iff (t : Term S ar X) : t.getName.isLeft ↔ ∃ c ts, t = con c ts := by
  cases t <;> simp

lemma getName_isRight_iff (t : Term S ar X) : t.getName.isRight ↔ ∃ x, t = var x := by
  cases t <;> simp

lemma eq_var_of_getName_isRight {t : Term S ar X} (h : t.getName.isRight) :
    t = var (t.getName.getRight h) := by
  cases t
  · simp
  · simp at h

@[reducible] def getAr : Term S ar X → ℕ
  | var _ => 0
  | con c _ => ar c

section Indexing

@[mk_iff]
inductive IsPos : Term S ar X → List ℕ → Prop
  | nil (t : Term S ar X) : t.IsPos []
  | con_cons {c : S} (ts : Fin (ar c) → Term S ar X) (i : ℕ) (hi : i < ar c) (p : List ℕ) :
    (ts ⟨i, hi⟩).IsPos p → (con c ts).IsPos (i :: p)

attribute [simp] IsPos.nil

lemma nil_isPos {t : Term S ar X} : t.IsPos [] := IsPos.nil t

@[simp] lemma isPos_var (x : X) (p : List ℕ) : (var (ar := ar) x).IsPos p ↔ p = [] := by
  rw [isPos_iff]
  simp

lemma IsPos.lt_getAr {t : Term S ar X} {i : ℕ} {p : List ℕ} (h : t.IsPos (i :: p)) :
    i < t.getAr := by
  cases h
  assumption

lemma cons_isPos (t : Term S ar X) (i : ℕ) (p : List ℕ) :
    t.IsPos (i :: p) ↔ ∃ (c : S) (ts : Fin (ar c) → Term S ar X) (hi : i < ar c),
      (ts ⟨i, hi⟩).IsPos p ∧ t = con c ts := by
  rw [isPos_iff]
  grind

lemma cons_isPos_con (c : S) (ts : Fin (ar c) → Term S ar X) (i : ℕ) (p : List ℕ) :
    (con c ts).IsPos (i :: p) ↔ ∃ (hi : i < ar c), (ts ⟨i, hi⟩).IsPos p := by
  constructor
  · rintro (_ | ⟨_, _, hi, _, h⟩)
    exact ⟨hi, h⟩
  · intro ⟨hi, h⟩
    exact IsPos.con_cons ts i hi p h

lemma IsPos.cons_fin {c : S} {ts : Fin (ar c) → Term S ar X} {i : Fin (ar c)} {p : List ℕ}
    (h : (ts i).IsPos p) : (con c ts).IsPos (↑i :: p) := con_cons ts i i.prop p h

lemma IsPos.of_append {t : Term S ar X} {p q : List ℕ} (h : t.IsPos (p ++ q)) : t.IsPos p := by
  induction p generalizing t with
  | nil => exact nil_isPos
  | cons i p ih =>
    obtain ⟨c, ts, hi, h', rfl⟩ := (cons_isPos ..).mp (List.cons_append ▸ h)
    exact con_cons ts i hi p (ih h')

lemma IsPos.of_prefix {t : Term S ar X} {p q : List ℕ} (hpq : p <+: q) (ht : t.IsPos q) :
    t.IsPos p := by
  obtain ⟨q, rfl⟩ := hpq
  exact ht.of_append

def getSubterm? : Term S ar X → List ℕ → Option (Term S ar X)
  | t, [] => some t
  | var _, _ :: _ => none
  | con c ts, i :: p => if hi : i < ar c then (ts ⟨i, hi⟩).getSubterm? p else none

lemma getSubterm?_isSome_iff_isPos (t : Term S ar X) (p : List ℕ) :
    (t.getSubterm? p).isSome ↔ t.IsPos p := by
  induction t generalizing p with
  | var => cases p <;> simp [getSubterm?]
  | con c ts ih =>
    cases p with
    | nil => simp [getSubterm?]
    | cons i p =>
      simp only [getSubterm?, cons_isPos_con]
      grind

instance (t : Term S ar X) (p : List ℕ) : Decidable (t.IsPos p) :=
  decidable_of_bool (t.getSubterm? p).isSome (getSubterm?_isSome_iff_isPos t p)

instance : GetElem (Term S ar X) (List ℕ) (Term S ar X) IsPos where
  getElem t p h := (t.getSubterm? p).get (getSubterm?_isSome_iff_isPos t p |>.mpr h)

instance : GetElem? (Term S ar X) (List ℕ) (Term S ar X) IsPos where
  getElem? := getSubterm?

instance : LawfulGetElem (Term S ar X) (List ℕ) (Term S ar X) IsPos where
  getElem?_def t p _ := by
    split
    · simp [getElem?, getElem]
    · simp_rw [getElem?, ←Option.not_isSome_iff_eq_none]
      rwa [getSubterm?_isSome_iff_isPos t p]

@[simp, grind =] lemma getElem?_nil (t : Term S ar X) : t[([] : List ℕ)]? = some t := by
  simp [getElem?, getSubterm?]

@[simp, grind =] lemma getElem_nil (t : Term S ar X) (h : t.IsPos []) : t[[]]'h = t := by
  simp [getElem, getSubterm?]

@[simp] lemma getElem?_cons (c : S) (ts : Fin (ar c) → Term S ar X) {i : ℕ} (hi : i < ar c)
    (p : List ℕ) : (con c ts)[i :: p]? = (ts ⟨i, hi⟩)[p]? := by simp [getElem?, getSubterm?, hi]

@[simp, grind =] lemma getElem_cons (c : S) (ts : Fin (ar c) → Term S ar X) {i : ℕ}
    (hi : i < ar c) (p : List ℕ) (h : (ts ⟨i, hi⟩).IsPos p) :
    (con c ts)[↑i :: p]'h.cons_fin = (ts ⟨i, hi⟩)[p] := by
  simp [getElem, getSubterm?, hi]

@[simp, grind =] lemma getElem_cons_fin (c : S) (ts : Fin (ar c) → Term S ar X) (i : Fin (ar c))
    (p : List ℕ) (h : (ts i).IsPos p) : (con c ts)[↑i :: p]'h.cons_fin = (ts i)[p] := by
  simp [getElem, getSubterm?]

lemma isPos_append_iff (t : Term S ar X) (p q : List ℕ) :
    t.IsPos (p ++ q) ↔ ∃ h : t.IsPos p, t[p].IsPos q := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    constructor
    · rw [List.cons_append, cons_isPos]
      rintro ⟨c, ts, hi, h, rfl⟩
      use (IsPos.con_cons ts i hi _ h).of_append
      grind
    · intro ⟨h, h'⟩
      rw [List.cons_append, cons_isPos]
      obtain ⟨c, ts, hi, hpos, rfl⟩ := cons_isPos t i p |>.mp h
      refine ⟨c, ts, hi, ?_, rfl⟩
      rw [getElem_cons _ _ hi _ hpos] at h'
      exact ih _ |>.mpr ⟨hpos, h'⟩

lemma IsPos.getElem_of_append {t : Term S ar X} {p q : List ℕ} (h : t.IsPos (p ++ q)) :
    (t[p]'h.of_append).IsPos q := by grind [isPos_append_iff]

lemma getElem?_append {t : Term S ar X} {p q : List ℕ} (h : t.IsPos p) :
    (t[p])[q]? = t[p ++ q]? := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    obtain ⟨c, ts, hi, hpos, rfl⟩ := cons_isPos t i p |>.mp h
    rw [getElem_cons c ts hi p hpos, ih hpos, List.cons_append, getElem?_cons c ts hi]

lemma getElem_append {t : Term S ar X} {p q : List ℕ} (hp : t.IsPos p) (hq : t[p].IsPos q) :
    t[p][q] = t[p ++ q]'(isPos_append_iff t p q |>.mpr ⟨hp, hq⟩) := by grind [getElem?_append]

@[mk_iff]
inductive IsVarPos : Term S ar X → List ℕ → Prop where
  | nil_var (x : X) : IsVarPos (var x) []
  | cons_con {c : S} (ts : Fin (ar c) → Term S ar X) {i : ℕ} (hi : i < ar c) (p : List ℕ) :
      (ts ⟨i, hi⟩).IsVarPos p → (con c ts).IsVarPos (i :: p)

lemma isVarPos_iff_isRight_getElem_getName (t : Term S ar X) (p : List ℕ) :
    t.IsVarPos p ↔ ∃ h : t.IsPos p, t[p].getName.isRight := by
  induction t generalizing p with
  | var x =>
    simp; grind [IsVarPos]
  | con c ts ih =>
    constructor
    · rintro (_ | ⟨_, hi, p, h⟩)
      obtain ⟨h, h'⟩ := ih ⟨_, hi⟩ p |>.mp h
      use h.con_cons
      simpa [getElem_cons c ts hi p h]
    · intro ⟨h, h'⟩
      cases p with
      | nil => simp_all
      | cons i p =>
        obtain ⟨hi, h⟩ := cons_isPos_con c ts i p |>.mp h
        rw [getElem_cons c ts hi p h] at h'
        exact IsVarPos.cons_con ts hi p <| ih ⟨i, hi⟩ p |>.mpr ⟨h, h'⟩

instance (t : Term S ar X) (p : List ℕ) : Decidable (t.IsVarPos p) :=
  decidable_of_iff' (∃ h : t.IsPos p, t[p].getName.isRight)
    (isVarPos_iff_isRight_getElem_getName t p)

lemma isVarPos_iff_getElem?_eq_some_var (t : Term S ar X) (p : List ℕ) :
    t.IsVarPos p ↔ ∃ x, t[p]? = some (var x) := by
  simp_rw [isVarPos_iff_isRight_getElem_getName, getName_isRight_iff]
  grind

lemma IsVarPos.isPos {t : Term S ar X} {p : List ℕ} (h : t.IsVarPos p) : t.IsPos p :=
  let ⟨h, _⟩ := isVarPos_iff_isRight_getElem_getName t p |>.mp h; h

lemma IsVarPos.isRight_getElem_getName {t : Term S ar X} {p : List ℕ} (h : t.IsVarPos p) :
  t[p]'h.isPos |>.getName.isRight := by grind [isVarPos_iff_isRight_getElem_getName]

def IsVarPos.getVar {t : Term S ar X} {p : List ℕ} (h : t.IsVarPos p) : X :=
  t[p]'h.isPos |>.getName.getRight h.isRight_getElem_getName

lemma IsVarPos.getElem_eq_var_getVar {t : Term S ar X} {p : List ℕ} (h : t.IsVarPos p) :
  t[p]'h.isPos = var h.getVar := by grind [getVar, eq_var_of_getName_isRight]

lemma IsVarPos.eq_of_prefix_of_isPos {t : Term S ar X} {p q : List ℕ} (hp : t.IsVarPos p)
    (hpq : p <+: q) (hq : t.IsPos q) : p = q := by
  obtain ⟨q, rfl⟩ := hpq
  obtain ⟨x, hx⟩ := isVarPos_iff_getElem?_eq_some_var t p |>.mp hp
  obtain ⟨_, heq⟩ := getElem_of_getElem? hx
  have := hq.getElem_of_append
  rw [heq, isPos_var] at this
  simp [this]

end Indexing

section Monad

protected def bind (t : Term S ar X) (f : X → Term S ar X') : Term S ar X' :=
  match t with
  | var x => f x
  | con c ts => con c (fun i => (ts i).bind f)

instance : Monad (Term S ar) where
  pure := var
  bind t m := t.bind m

@[simp, grind =] lemma var_bind (x : X) (f : X → Term S ar X') : var x >>= f = f x := rfl

@[simp, grind =] lemma con_bind {c : S} (ts : Fin (ar c) → Term S ar X) (f : X → Term S ar X') :
    con c ts >>= f = con c (ts · >>= f) := rfl

@[simp, grind =] lemma var_map (x : X) (f : X → X') : f <$> (var (ar := ar) x) = var (f x) := rfl

@[simp, grind =] lemma con_map {c : S} (ts : Fin (ar c) → Term S ar X) (f : X → X') :
    f <$> con c ts = con c (f <$> ts ·) := rfl

instance : LawfulMonad (Term S ar) :=
  LawfulMonad.mk' (Term S ar) (by intro _ t; induction t <;> simp_all) (by simp [pure])
  (by intro _ _ _ t f g; induction t <;> simp_all)

def mapCon (t : Term S ar X) (f : S → S') (hf : ∀ c, ar' (f c) = ar c) : Term S' ar' X :=
  match t with
  | var x => var x
  | con c ts => con (f c) (fun i => (ts <| i.cast (hf c)).mapCon f hf)

lemma mapCon_bind_comm (t : Term S ar X) {f : S → S'} (hf : ∀ c, ar' (f c) = ar c)
    (g : X → Term S ar X') :
    (t >>= g).mapCon f hf = t.mapCon f hf >>= (fun x => (g x).mapCon f hf) := by
  induction t <;> simp_all [mapCon]

lemma mapCon_map_comm (t : Term S ar X) {f : S → S'} (hf : ∀ c, ar' (f c) = ar c)
    (g : X → X') : (g <$> t).mapCon f hf = g <$> t.mapCon f hf := by
  simp_rw [←bind_pure_comp, mapCon_bind_comm]
  congr

lemma IsPos.bind {t : Term S ar X} {p : List ℕ} (h : t.IsPos p) (f : X → Term S ar X') :
    (t >>= f).IsPos p := by
  induction t generalizing p with
  | var => simp_all
  | con c ts ih =>
    cases p with
    | nil => simp
    | cons i p =>
      obtain ⟨hi, h⟩ := (cons_isPos_con c ts i p).mp h
      rw [con_bind, cons_isPos_con c (ts · >>= f) i p]
      exact ⟨hi, ih ⟨i, hi⟩ h⟩

lemma getElem_bind {t : Term S ar X} {p : List ℕ} (h : t.IsPos p) (f : X → Term S ar X') :
    (t >>= f)[p]'(h.bind f) = t[p] >>= f := by
  induction t generalizing p with
  | var => simp at h; simp_all
  | con c ts ih =>
    cases p with
    | nil => simp
    | cons i p =>
      obtain ⟨hi, h⟩ := (cons_isPos_con c ts i p).mp h
      simp [getElem_cons c ts hi p h, getElem_cons c (ts · >>= f) hi p (h.bind f), ←ih]

end Monad

section Shape

inductive IsSubshape : Term S ar X → Term S ar Y → Prop where
  | refl_var (x : X) (y : Y) : (var x).IsSubshape (var y)
  | prune (x : X) (t : Term S ar Y) : (var x).IsSubshape t
  | congr_con (c : S) {ss : Fin (ar c) → Term S ar X} {ts : Fin (ar c) → Term S ar Y}
      (h : ∀ i, (ss i).IsSubshape (ts i)) : (con c ss).IsSubshape (con c ts)

scoped infix:50 " ⊑ " => IsSubshape

@[refl]
lemma IsSubshape.refl (t : Term S ar X) : t ⊑ t := by
  induction t with
  | var x => exact refl_var x x
  | con c _ ih => exact congr_con c ih

lemma IsSubshape.trans {s : Term S ar X} {t : Term S ar Y} {u : Term S ar Z}
    (hst : s ⊑ t) (htu : t ⊑ u) : s ⊑ u := by
  induction hst generalizing u with
  | refl_var x => exact prune x u
  | prune x => exact prune x u
  | congr_con c h ih =>
    cases htu with
    | congr_con _ h' => exact congr_con c (fun i => ih i (h' i))

instance : IsPreorder (Term S ar X) (· ⊑ ·) where
  refl := IsSubshape.refl
  trans _ _ _ := IsSubshape.trans

lemma IsSubshape.var_iff (t : Term S ar X) (y : Y) : t ⊑ var y ↔ ∃ x, t = var x := by
  constructor
  · rintro (⟨x, _⟩ | ⟨x, _⟩ | _)
    · use x
    · use x
  · rintro ⟨x, rfl⟩
    exact .prune x (var y)

lemma IsSubshape.con_con_iff (c c' : S) (ss : Fin (ar c) → Term S ar X)
    (ts : Fin (ar c') → Term S ar Y) :
    (con c ss) ⊑ (con c' ts) ↔ ∃ (h : c = c'), ∀ i, ss i ⊑ ts (h ▸ i) := by
  constructor
  · rintro (_ | _ | ⟨ts, h⟩)
    use rfl
  · rintro ⟨rfl, h⟩
    exact congr_con c h

instance [Subsingleton X] : IsPartialOrder (Term S ar X) (· ⊑ ·) where
  antisymm s t h h' := by
    induction h with
    | refl_var x y =>
      congr
      exact Subsingleton.elim ..
    | prune x t =>
      obtain ⟨x', rfl⟩ := IsSubshape.var_iff t x |>.mp h'
      congr
      exact Subsingleton.elim ..
    | congr_con _ _ ih =>
      cases h' with
      | congr_con _ h' =>
        congr
        ext i
        exact ih i (h' i)

def shape (t : Term S ar X) : Term S ar PUnit.{u + 1} := (fun _ => .unit) <$> t

@[simp] lemma map_shape (f : X → X') (t : Term S ar X) : (f <$> t).shape = t.shape := by
  simp [shape]

@[simp] lemma shape_shape (t : Term S ar X) : t.shape.shape = t.shape := by simp [shape]

theorem subshape_iff_shape_subshape (s : Term S ar X) (t : Term S ar Y) :
    s ⊑ t ↔ s.shape ⊑ t.shape := by
  induction s generalizing t with
  | var => simp [shape, IsSubshape.prune]
  | con c ss ih =>
    cases t with
    | var => simp [IsSubshape.var_iff, shape]
    | con c ts =>
      constructor
      · rintro (_ | _ | ⟨_, h⟩)
        exact IsSubshape.congr_con c fun i => (ih i _).mp (h i)
      · simp_rw [shape, con_map]
        rintro (_ | _ | ⟨_, h⟩)
        exact IsSubshape.congr_con c fun i => (ih i _).mpr (h i)

lemma IsSubshape.map_map_iff (f : X → X') (g : Y → Y') {s : Term S ar X} {t : Term S ar Y} :
    s ⊑ t ↔ f <$> s ⊑ g <$> t := by
  rw (occs := [2]) [subshape_iff_shape_subshape]
  rw [subshape_iff_shape_subshape, map_shape, map_shape]

lemma IsSubshape.map_map (f : X → X') (g : Y → Y') {s : Term S ar X} {t : Term S ar Y} (h : s ⊑ t) :
    f <$> s ⊑ g <$> t := IsSubshape.map_map_iff f g |>.mp h

lemma IsSubshape.map_map_self (f : X → Y) (g : X → Z) (t : Term S ar X) : f <$> t ⊑ g <$> t :=
  (IsSubshape.refl t).map_map f g

lemma IsSubshape.bind (t : Term S ar X) (f : X → Term S ar X') : t ⊑ t >>= f := by
  induction t with
  | var x => exact prune x (f x)
  | con c ts ih => exact congr_con c ih

end Shape

section LudicOrder

instance [Bot X] : Bot (Term S ar X) := ⟨var ⊥⟩

instance [Top X] : Top (Term S ar X) := ⟨var ⊤⟩

inductive CongrGen (r : Term S ar X → Term S ar X → Prop) : Term S ar X → Term S ar X → Prop where
  | ax {s t : Term S ar X} (h : r s t) : CongrGen r s t
  | refl (t : Term S ar X) : CongrGen r t t
  | trans {s t u : Term S ar X} (hst : CongrGen r s t) (htu : CongrGen r t u) : CongrGen r s u
  | congr_con (c : S) {ts ts' : Fin (ar c) → Term S ar X} (h : ∀ i, CongrGen r (ts i) (ts' i)) :
      CongrGen r (con c ts) (con c ts')

lemma congrGen_le_of_le {r r' : Term S ar X → Term S ar X → Prop} (hle : r ≤ r') :
    CongrGen r ≤ CongrGen r' := by
  intro t u h
  induction h
  case ax h => exact .ax (hle _ _ h)
  all_goals grind [CongrGen]

instance (r : Term S ar X → Term S ar X → Prop) : Std.Refl (CongrGen r) := ⟨.refl⟩

instance (r : Term S ar X → Term S ar X → Prop) : IsTrans _ (CongrGen r) := ⟨fun _ _ _ => .trans⟩

inductive StableLE [Bot X] : Term S ar X → Term S ar X → Prop where
  | fid (t : Term S ar X) : StableLE ⊥ t
  | refl (t : Term S ar X) : StableLE t t
  | congr_con (c : S) {ts ts' : Fin (ar c) → Term S ar X} (h : ∀ i, StableLE (ts i) (ts' i)) :
      StableLE (con c ts) (con c ts')

lemma StableLE.trans [Bot X] {s t u : Term S ar X} (hst : s.StableLE t) (htu : t.StableLE u) :
    s.StableLE u := by
  induction hst generalizing u with
  | fid => exact .fid u
  | refl => exact htu
  | congr_con c h ih =>
    cases htu with
    | refl => exact .congr_con c h
    | congr_con _ h' => exact .congr_con c (fun i => ih i (h' i))

lemma StableLE.antisymm [Bot X] {s t : Term S ar X} (hst : s.StableLE t) (hts : t.StableLE s) :
    s = t := by
  induction hst with
  | fid => cases hts <;> rfl
  | refl => rfl
  | congr_con c _ ih =>
    cases hts with
    | refl => rfl
    | congr_con _ h' =>
      congr
      ext i
      exact ih i (h' i)

instance [Bot X] : IsPartialOrder (Term S ar X) StableLE where
  refl := .refl
  trans _ _ _ := .trans
  antisymm _ _ := StableLE.antisymm

inductive PruneLE [Top X] : Term S ar X → Term S ar X → Prop where
  | dai (t : Term S ar X) : PruneLE t ⊤
  | refl (t : Term S ar X) : PruneLE t t
  | congr_con (c : S) {ts ts' : Fin (ar c) → Term S ar X} (h : ∀ i, PruneLE (ts i) (ts' i)) :
      PruneLE (con c ts) (con c ts')

lemma PruneLE.trans [Top X] {s t u : Term S ar X} (hst : s.PruneLE t) (htu : t.PruneLE u) :
    s.PruneLE u := by
  induction htu generalizing s with
  | dai => exact .dai s
  | refl => exact hst
  | congr_con c h ih =>
    cases hst with
    | refl => exact .congr_con c h
    | congr_con c h' => exact .congr_con c (fun i => ih i (h' i))

lemma PruneLE.antisymm [Top X] {s t : Term S ar X} (hst : s.PruneLE t) (hts : t.PruneLE s) :
    s = t := by
  induction hst with
  | dai => cases hts <;> rfl
  | refl => rfl
  | congr_con c _ ih =>
    cases hts with
    | refl => rfl
    | congr_con _ h' =>
      congr
      ext i
      exact ih i (h' i)

instance [Top X] : IsPartialOrder (Term S ar X) PruneLE where
  refl := .refl
  trans _ _ _ := .trans
  antisymm _ _ := PruneLE.antisymm

lemma stableLE_pruneLE_comm [Bot X] [Top X] {s t u : Term S ar X} (hst : StableLE s t)
    (htu : PruneLE t u) : ∃ v, PruneLE s v ∧ StableLE v u := by
  induction hst generalizing u with
  | fid => use ⊥, .refl ⊥, .fid u
  | refl => use u, htu, .refl u
  | @congr_con c ss ts hst ih =>
    cases htu with
    | dai => use ⊤, .dai (con c ss), .refl ⊤
    | refl _ => use con c ss, .refl _, .congr_con c hst
    | @congr_con c _ us htu =>
      choose! vs hsv hvu using fun i => ih i (u := us i)
      refine ⟨con c vs, .congr_con c ?_, .congr_con c ?_⟩
        <;> grind

def ExtLE [Bot X] [Top X] : Term S ar X → Term S ar X → Prop := CongrGen (fun s t => s = ⊥ ∨ t = ⊤)

lemma StableLE.extLE [Bot X] [Top X] {s t : Term S ar X} (h : s.StableLE t) : s.ExtLE t := by
  induction h with
  | fid t => exact .ax (Or.inl rfl)
  | refl t => exact .refl t
  | congr_con c h ih => exact .congr_con c ih

lemma stableLE_le_extLE [Bot X] [Top X] : StableLE (ar := ar) (X := X) ≤ ExtLE :=
  fun _ _ => StableLE.extLE

lemma PruneLE.extLE [Bot X] [Top X] {s t : Term S ar X} (h : s.PruneLE t) : s.ExtLE t := by
  induction h with
  | dai t => exact .ax (Or.inr rfl)
  | refl t => exact .refl t
  | congr_con c h ih => exact .congr_con c ih

lemma pruneLE_le_extLE [Bot X] [Top X] : PruneLE (ar := ar) (X := X) ≤ ExtLE :=
  fun _ _ => PruneLE.extLE

theorem extLE_iff [Bot X] [Top X] (s t : Term S ar X) :
    s.ExtLE t ↔ ∃ u, s.PruneLE u ∧ u.StableLE t := by
  refine ⟨?_, fun ⟨_, h, h'⟩ => h.extLE.trans h'.extLE⟩
  intro h
  induction h with
  | @ax s t h =>
    rcases h with (rfl | rfl)
    · use ⊥, .refl ⊥, .fid _
    · use ⊤, .dai _, .refl ⊤
  | refl t => use t, .refl t, .refl t
  | @trans s t u hst htu ih₁ ih₂ =>
    obtain ⟨v₁, hsv₁, hv₁t⟩ := ih₁
    obtain ⟨v₂, htv₂, hv₂u⟩ := ih₂
    obtain ⟨v, hv_prune, hv_stable⟩ := stableLE_pruneLE_comm hv₁t htv₂
    use v, hsv₁.trans hv_prune, hv_stable.trans hv₂u
  | congr_con c h ih =>
    choose us hsu hut using ih
    use con c us, .congr_con c hsu, .congr_con c hut

theorem extLE_eq_comp [Bot X] [Top X] :
    ExtLE (ar := ar) (X := X) = Relation.Comp PruneLE StableLE := by
  ext s t
  exact extLE_iff s t

end LudicOrder

section Trace

@[mk_iff]
inductive IsTrace : Term S ar X → List S → Prop where
  | nil (t : Term S ar X) : t.IsTrace []
  | con_singleton (c : S) (ts : Fin (ar c) → Term S ar X) : (con c ts).IsTrace [c]
  | con_cons (c : S) (ts : Fin (ar c) → Term S ar X) {i : Fin (ar c)} {μ : List S} :
      (ts i).IsTrace μ → (con c ts).IsTrace (c :: μ)

@[simp] lemma isTrace_var_iff (x : X) (μ : List S) : (var (ar := ar) x).IsTrace μ ↔ μ = [] := by
  rw [isTrace_iff]
  simp

lemma isTrace_con_cons_iff (c : S) (ts : Fin (ar c) → Term S ar X) (c' : S) (μ : List S) :
    (con c ts).IsTrace (c' :: μ) ↔ c = c' ∧ (μ = [] ∨ ∃ i, (ts i).IsTrace μ) := by
  constructor
  · intro h
    cases h
    case con_cons i h => exact ⟨rfl, Or.inr ⟨i, h⟩⟩
    case con_singleton => exact ⟨rfl, Or.inl rfl⟩
  · rintro ⟨rfl, (rfl | ⟨i, h⟩)⟩
    · exact IsTrace.con_singleton c ts
    · exact h.con_cons c ts

def traces : Term S ar X → List (List S)
  | var _ => [[]]
  | con c ts => [[], [c]] ++ (List.ofFn fun i => (ts i).traces).flatten.map (c :: ·)

theorem isTrace_iff_mem_traces (t : Term S ar X) (μ : List S) : t.IsTrace μ ↔ μ ∈ t.traces := by
  induction t generalizing μ with
  | var => simp [traces]
  | con c ts ih =>
    cases μ with
    | nil => simp [IsTrace.nil, traces]
    | cons c' μ => simp [isTrace_con_cons_iff, traces]; grind

instance [DecidableEq S] (t : Term S ar X) (μ : List S) : Decidable (t.IsTrace μ) :=
  decidable_of_iff' (μ ∈ t.traces) (isTrace_iff_mem_traces t μ)

theorem IsSubshape.isTrace_of_isTrace {s : Term S ar X} {t : Term S ar Y} (h : s ⊑ t) {μ : List S}
    (hμ : s.IsTrace μ) : t.IsTrace μ := by
  induction h generalizing μ with
  | refl_var => simpa using hμ
  | prune x t => exact isTrace_var_iff x μ |>.mp hμ ▸ IsTrace.nil t
  | congr_con c h ih =>
    cases μ with
    | nil => exact IsTrace.nil _
    | cons c' μ =>
      obtain ⟨rfl, (rfl | ⟨i, h⟩)⟩ := isTrace_con_cons_iff _ _ _ _ |>.mp hμ
      · exact IsTrace.con_singleton ..
      · exact IsTrace.con_cons c _ <| ih _ h

theorem IsTrace.map_iff (t : Term S ar X) (f : X → X') (μ : List S) :
    (f <$> t).IsTrace μ ↔ t.IsTrace μ := by
  constructor
  · simpa using (IsSubshape.map_map_self f id t).isTrace_of_isTrace (μ := μ)
  · simpa using (IsSubshape.map_map_self id f t).isTrace_of_isTrace (μ := μ)

lemma IsTrace.shape_iff (t : Term S ar X) (μ : List S) : t.IsTrace μ ↔ t.shape.IsTrace μ :=
  map_iff t (fun _ => PUnit.unit) μ |>.symm

end Trace

end Term
