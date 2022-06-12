import tactic
import ssyt

/-

Defining "inverse_row_bump_step": one step of inverse row insertion

Given an ssyt T and natural numbers i, k, we "inverse bump" k into row i
while preserving semistandardness. In particular k goes before any existing k's
and replaces the rightmost smaller entry. (It is necessary that there exist an entry
smaller than k in row i.)

An assumption is necessary (to preserve column strictness) for this to be legal.
  [ssyt.irbs_cert]
  [ssyt.irbs_cert.legal_of_cert]

The bump position is defined using finset.max'.
  [ssyt.irbc]
  
The bump itself uses ssyt.legal.replace.
  [ssyt.irbs]

-/

section inverse_row_bump_column

def ssyt.irbc_strip {μ : young_diagram} (T : ssyt μ) (i val : ℕ) : finset ℕ :=
  ((finset.range $ μ.row_len i).filter (λ j, T i j < val))

lemma ssyt.irbc_strip_mem {μ : young_diagram} (T : ssyt μ) {i val j : ℕ} :
  j ∈ T.irbc_strip i val ↔ (i, j) ∈ μ ∧ T i j < val :=
by rw [ssyt.irbc_strip, finset.mem_filter, finset.mem_range, μ.mem_row_iff']

lemma ssyt.irbc_aux {μ : young_diagram} (T : ssyt μ) {i val : ℕ} :
  (T.irbc_strip i val).nonempty ↔ ∃ j, (i, j) ∈ μ ∧ T i j < val :=
begin
  simp_rw ← T.irbc_strip_mem, refl,
end

def ssyt.irbc {μ : young_diagram} (T : ssyt μ) {i val : ℕ}
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) : ℕ :=
finset.max' _ $ T.irbc_aux.mpr exists_lt

lemma ssyt.irbc_cell_and_lt_val {μ : young_diagram} (T : ssyt μ) {i val : ℕ}
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) :
(i, T.irbc exists_lt) ∈ μ ∧ T i (T.irbc exists_lt) < val :=
begin
  rw ← T.irbc_strip_mem, apply finset.max'_mem,
end

lemma ssyt.irbc_lt_iff {μ : young_diagram} (T : ssyt μ) {i val : ℕ}
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) (j : ℕ) :
  T.irbc exists_lt < j ↔ (i, j) ∈ μ → val ≤ T i j :=
begin
  simp_rw [ssyt.irbc, finset.max'_lt_iff, ssyt.irbc_strip_mem],
  rw ← not_iff_not, push_neg,
  split,
  rintro ⟨j', ⟨cell', hj'⟩, hj''⟩,
  exact ⟨μ.nw_of (by refl) hj'' cell',
         lt_of_le_of_lt (T.row_weak' hj'' cell') hj'⟩,
  intro hj, exact ⟨j, hj, by refl⟩,
end

lemma ssyt.le_irbc_iff {μ : young_diagram} (T : ssyt μ) {i val : ℕ}
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) (j : ℕ) :
  j ≤ T.irbc exists_lt ↔ (i, j) ∈ μ ∧ T i j < val :=
begin
  rw [← not_iff_not], push_neg, rw ssyt.irbc_lt_iff,
end

lemma ssyt.irbc_le_iff {μ : young_diagram} (T : ssyt μ) {i val : ℕ}
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) (j : ℕ) :
  T.irbc exists_lt ≤ j ↔ ∀ j' > j, (i, j') ∈ μ → val ≤ T i j' :=
begin
  rw [ssyt.irbc, finset.max'_le_iff],
  apply forall_congr, intro a,
  rw [ssyt.irbc_strip_mem, ← not_imp_not], push_neg, refl,
end

lemma ssyt.lt_irbc_iff {μ : young_diagram} (T : ssyt μ) {i val : ℕ}
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) (j : ℕ) :
  j < T.irbc exists_lt ↔ ∃ j' > j, (i, j') ∈ μ ∧ T i j' < val :=
begin
  rw ← not_iff_not, push_neg, rw ssyt.irbc_le_iff,
end

lemma ssyt.irbc_eq_iff {μ : young_diagram} (T : ssyt μ) {i val : ℕ}
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) (j : ℕ) :
  T.irbc exists_lt = j ↔
  (i, j) ∈ μ ∧ T i j < val ∧ (∀ j' > j, (i, j') ∈ μ → val ≤ T i j') :=
begin
  rw [eq_comm, eq_iff_le_not_lt], push_neg,
  rw [ssyt.le_irbc_iff, ssyt.irbc_le_iff, and_assoc],
end

lemma ssyt.irbc_eq_of_eq_row
  {μ ν : young_diagram} (T : ssyt μ) (T' : ssyt ν) {i val : ℕ}
  (eq_cell : ∀ {j}, (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_row : ∀ {j}, T i j = T' i j)
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val)
  (exists_lt' : ∃ j, (i, j) ∈ ν ∧ T' i j < val := by {
    obtain ⟨j, hj⟩ := exists_lt, rw [eq_cell, eq_row] at hj, exact ⟨j, hj⟩
  }) :
  T.irbc exists_lt = T'.irbc exists_lt' :=
begin
  rw T.irbc_eq_iff,
  -- change first statement
  rw [eq_cell, eq_row],
  -- change second statement
  simp_rw [eq_cell, eq_row],
  rw ← T'.irbc_eq_iff,
end

lemma ssyt.irbc_eq_of_eq_row'
  {μ ν : young_diagram} (T : ssyt μ) (T' : ssyt ν) {i val i' val' : ℕ}
  (eq_cell : ∀ {j}, (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_row : ∀ {j}, T i j = T' i j)
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val)
  (exists_lt' : ∃ j, (i', j) ∈ ν ∧ T' i' j < val')
  (hi : i' = i) (hval : val' = val) :
  T.irbc exists_lt = T'.irbc exists_lt' :=
begin
  rw T.irbc_eq_iff,
  simp_rw [eq_cell, eq_row, ← hi, ← hval],
  rw ← T'.irbc_eq_iff,
end


end inverse_row_bump_column

section inverse_row_bump_step

section irbs_cert

structure ssyt.irbs_cert {μ : young_diagram} (T : ssyt μ) :=
  (i val : ℕ)
  (exists_lt : ∃ j, (i, j) ∈ μ ∧ T i j < val) -- can just use 0!
  (down : ∀ i', i < i' → (i', T.irbc exists_lt) ∈ μ → 
    val < T i' (T.irbc exists_lt))

@[reducible]
def ssyt.irbs_cert.j {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : ℕ :=
  T.irbc h.exists_lt

@[reducible]
def ssyt.irbs_cert.out {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : ℕ :=
  T h.i h.j

lemma ssyt.irbs_cert.cell {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) :
  (h.i, h.j) ∈ μ := (T.irbc_cell_and_lt_val h.exists_lt).1

lemma ssyt.irbs_cert.out_lt_val {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) :
  h.out < h.val := (T.irbc_cell_and_lt_val h.exists_lt).2

def ssyt.irbs_cert.to_legal {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) :
  T.legal :=
{ i := h.i,
  j := h.j,
  val := h.val,
  cell_left := λ j hj, μ.nw_of (by refl) (le_of_lt hj) h.cell,
  cell_up := λ i hi, μ.nw_of (le_of_lt hi) (by refl) h.cell,
  left := λ j hj, (T.row_weak hj h.cell).trans (le_of_lt h.out_lt_val),
  right := λ j hj cell, (T.irbc_lt_iff h.exists_lt _).mp hj cell,
  up := λ i hi, (T.col_strict hi h.cell).trans h.out_lt_val,
  down := h.down }

lemma ssyt.exists_lt_of_del_inner {μ : young_diagram} (T : ssyt μ)
  (c : μ.inner_corner) (hc : c.i ≠ 0) :
  ∃ j, (c.i.pred, j) ∈ c.del ∧ (T.del c) c.i.pred j < T c.i c.j :=
begin
  use c.j,
  have not_cell : (c.i.pred, c.j) ≠ (c.i, c.j) := 
    λ h, (ne_of_lt (nat.pred_lt hc)) (prod.mk.inj_right c.j h),
  rw [c.mem_del, T.del_entry, if_neg not_cell],
  exact ⟨⟨not_cell, μ.nw_of (nat.pred_le _) (by refl) c.cell⟩,
          T.col_strict (nat.pred_lt hc) c.cell⟩,
end

def ssyt.irbs_cert_of_inner_corner  {μ : young_diagram} (T : ssyt μ)
  (c : μ.inner_corner) (hc : c.i ≠ 0) : (T.del c).irbs_cert :=
{ i := c.i.pred,
  val := T c.i c.j,
  exists_lt := T.exists_lt_of_del_inner c hc,
  down := λ i' hi' cell', begin
    suffices : c.j ≤ (T.del c).irbc (T.exists_lt_of_del_inner c hc),
      have cell := c.del.nw_of (nat.le_of_pred_lt hi') this cell',
      rw c.mem_del at cell, exfalso, exact cell.1 rfl,

    have hi_ne : c.i.pred ≠ c.i := ne_of_lt (nat.pred_lt hc),
    rw [ssyt.le_irbc_iff, c.mem_del, T.del_entry_eq_of_ne_row hi_ne],
    split, split, 
    exact λ h, hi_ne (prod.mk.inj_right c.j h),
    exact μ.nw_of (nat.pred_le _) (by refl) c.cell,
    exact T.col_strict (nat.pred_lt hc) c.cell,
  end,
}

def ssyt.irbs_cert.copy {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {ν : young_diagram} (T' : ssyt ν)
  (eq_cell : ∀ i j (hi : h.i ≤ i), (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_ge_row : ∀ i j (hi : h.i ≤ i), T i j = T' i j) : T'.irbs_cert :=
{ i := h.i, val := h.val,
  exists_lt := begin
    simp_rw [← eq_cell _ _ (le_refl _), ← eq_ge_row _ _ (le_refl _)],
    exact h.exists_lt,
  end,
  down := λ i' hi', begin
    rw [← eq_cell _ _ (le_of_lt hi'), ← eq_ge_row _ _ (le_of_lt hi')],
    rw ← T.irbc_eq_of_eq_row T',
    exact h.down i' hi',
    exact λ j, eq_cell _ _ (by refl),
    exact λ j, eq_ge_row _ _ (by refl),
  end
}

end irbs_cert

section irbs

def ssyt.irbs_cert.irbs {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : 
  ssyt μ := h.to_legal.replace h.cell

lemma ssyt.irbs_cert.irbs_entry {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  (i j : ℕ) : h.irbs i j = ite ((i, j) = (h.i, h.j)) h.val (T i j) := rfl

lemma ssyt.irbs_cert.irbs_wt {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  (val : ℕ) : 
  h.irbs.wt val + ite (val = T h.i h.j) 1 0 = T.wt val + ite (val = h.val) 1 0 :=
by apply ssyt.wt_replace

lemma ssyt.irbs_cert.irbs_entry_eq_of_ne_row {μ : young_diagram} {T : ssyt μ} 
  (h : T.irbs_cert) {i j : ℕ} (hi : i ≠ h.i) : h.irbs i j = T i j :=
begin
  rw [h.irbs_entry, if_neg], rintro ⟨⟩, exact hi rfl
end

lemma ssyt.irbs_cert.next_exists_lt {μ : young_diagram} {T : ssyt μ} 
  (h : T.irbs_cert) (hi_pos : h.i ≠ 0) : 
  ∃ (j : ℕ), (h.i.pred, j) ∈ μ ∧ (h.irbs) h.i.pred j < h.out :=
begin
  use h.j, split,
  apply μ.nw_of (nat.pred_le _) (le_refl _) h.cell,
  rw h.irbs_entry_eq_of_ne_row (ne_of_lt (nat.pred_lt hi_pos)),
  exact T.col_strict (nat.pred_lt hi_pos) h.cell,
end

lemma ssyt.irbs_cert.le_next_irbc {μ : young_diagram} {T : ssyt μ} 
  (h : T.irbs_cert) (hi_pos : h.i ≠ 0) :
  h.j ≤ h.irbs.irbc (h.next_exists_lt hi_pos) :=
begin
  rw ssyt.le_irbc_iff, split, exact μ.nw_of (nat.pred_le _) (by refl) h.cell,
  rw h.irbs_entry_eq_of_ne_row (ne_of_lt _),
  apply T.col_strict _ h.cell,
  all_goals {exact nat.pred_lt hi_pos},
end

@[simps]
def ssyt.irbs_cert.next_cert {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  (hi_pos : h.i ≠ 0) : h.irbs.irbs_cert :=
{ i := h.i.pred,
  val := h.out,
  exists_lt := begin
    use h.j, split,
    apply μ.nw_of (nat.pred_le _) (le_refl _) h.cell,
    rw h.irbs_entry_eq_of_ne_row (ne_of_lt (nat.pred_lt hi_pos)),
    exact T.col_strict (nat.pred_lt hi_pos) h.cell,
  end,
  down := λ i' hi' cell', begin
    replace hi' := nat.le_of_pred_lt hi',
    apply le_trans _ (h.irbs.col_weak hi' cell'),
    apply lt_of_lt_of_le h.out_lt_val,
    apply le_trans _ (h.irbs.row_weak' (h.le_next_irbc hi_pos) _),
    rw h.irbs_entry, split_ifs; refl,
    exact μ.nw_of hi' (by refl) cell',
  end
}

-- what is the correct "lexicographic" fact here?
-- (the inverse fact to [row_insertion.lean/ssyt.rbs_cert.rbc_lt_rbc] ?)

-- if we inverse-bump a second corner west of the first one, the resulting out-value
-- is ≤ the first one

-- intermediate stage: if we inverse-bump in the same row with a value k' s.t.
-- k' ≤ k, then j' < j and out' ≤ out

lemma ssyt.irbs_cert.irbc_lt_irbc {μ : young_diagram} {T : ssyt μ} 
  (h : T.irbs_cert) (h' : h.irbs.irbs_cert)
  (hi : h'.i = h.i) (hval : h'.val ≤ h.val) :
  h'.j < h.j :=
begin
  rw ssyt.irbc_lt_iff, intro _, rwa [hi, h.irbs_entry, if_pos rfl],
end

lemma ssyt.irbs_cert.irbc_out_le_irbc_out {μ : young_diagram} {T : ssyt μ} 
  (h : T.irbs_cert) (h' : h.irbs.irbs_cert)
  (hi : h'.i = h.i) (hval : h'.val ≤ h.val) :
  h'.out ≤ h.out :=
begin
  have hj : h'.j < h.j := h.irbc_lt_irbc h' hi hval,
  rw [ssyt.irbs_cert.out, h.irbs_entry, hi, if_neg],
  exact T.row_weak hj h.cell,
  exact λ h, (ne_of_lt hj) (prod.mk.inj_left _ h),
end

end irbs

end inverse_row_bump_step