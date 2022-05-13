import tactic
import ssyt

/-

Defining "row_bump_step": one step of row insertion

Given an ssyt T and natural numbers i, k, we "bump" k into row i
while preserving semistandardness. In particular k goes after any existing k's
and either replaces the leftmost larger entry, or if there are no entries > k, it is
added at the end of the row.

An assumption is necessary (to preserve column strictness) for this to be legal.
  [ssyt.rbs_cert]
  [ssyt.rbs_cert.legal_of_cert]

The bump position is defined using nat.find.
  [ssyt.rbc]
  
The bump itself is either ssyt.legal.replace or ssyt.legal.add.
  [ssyt.rbs]
  [ssyt.rbs_end]

Two key lemmas are:
  1. The removed entry from row i is itself legal for bumping into row i+1.
    [ssyt.rbs_cert.next_cert]
  2. If so, the (i+1)st row bump column is ≤ the ith row bump column.
    [ssyt.rbs_cert.next_rbc_le]
  3. If we insert k, followed by k' ≥ k, in the same row, the k' bump column is 
    *strictly* to the right (larger) than the k column, and the bumped-out
    entry is weakly larger than the first bumped-out entry.
    [ssyt.rbs_cert.rbc_lt_rbc]
    [ssyt.rbs_cert.rbc_out_le_rbc_out]
Lemma 2 is proven in more generality. Lemmas 1-2 are used to define
row insertion by successive row bump steps.
Lemma 3 is used to prove that the recording tableau is semistandard,
which is currently a hard proof (see [row_bump.lean/ssyt.rbs_cert.rbwf_pieri]).

Various independence lemmas are shown for later use:
 * the insertion only affects row i
    [ssyt.rbs_entry_eq_of_ne_row]
    [ssyt.rbs_cert.rbs_end_shape_eq_of_ne_row]
    [ssyt.rbs_cert.rbs_end_entry_eq_of_ne_row]
 * the insertion column only depends on row i
    [ssyt.rbc_eq_of_eq_row]
 * the extra assumption for column-strictness only depends on rows ≤ i
    [ssyt.rbs_cert.copy]
    [ssyt.rbs_cert.copy']
 * commutativity of two rbs steps in different rows: 
    [ssyt.rbs_cert.rbs_comm]
   Note: this is _not_ currently used anywhere, but it might be possible to
    use it to golf [row_bump.lean/ssyt.rbs_cert.rbwf_pieri].

Finally, auxiliary facts are shown about the size and weight of the tableau.
  [ssyt.rbs_cert.rbs_wt]
  [ssyt.rbs_cert.rbs_end_size]
  [ssyt.rbs_cert.rbs_end_wt]
-/

section row_bump_column

lemma ssyt.rbc_aux {μ : young_diagram} (T : ssyt μ) (i val : ℕ) :
  ∃ j, (i, j) ∉ μ ∨ val < T i j :=
exists_or_distrib.mpr $ or.inl $ μ.row_len_aux i

def ssyt.rbc {μ : young_diagram} (T : ssyt μ) (i val : ℕ) : ℕ :=
  nat.find $ T.rbc_aux i val

lemma ssyt.lt_rbc_iff {μ : young_diagram} (T : ssyt μ) {i j val: ℕ} :
  j < T.rbc i val ↔ (i, j) ∈ μ ∧ T i j ≤ val :=
begin
  rw [ssyt.rbc, nat.lt_find_iff], push_neg,
  exact ⟨λ h, h _ (le_refl _),
         λ h _ hm, ⟨μ.nw_of (le_refl _) hm h.1, (T.row_weak' hm h.1).trans h.2⟩⟩
end

lemma ssyt.rbc_le_iff {μ : young_diagram} (T : ssyt μ) {i j val: ℕ} :
  T.rbc i val ≤ j ↔ (i, j) ∉ μ ∨ val < T i j :=
begin
  rw ← not_iff_not, push_neg, apply ssyt.lt_rbc_iff
end

lemma ssyt.rbc_not_cell_or_val_lt {μ : young_diagram} (T : ssyt μ) (i val: ℕ) :
  (i, T.rbc i val) ∉ μ ∨ val < T i (T.rbc i val) :=
nat.find_spec (T.rbc_aux i val)

lemma ssyt.rbc_eq_iff {μ : young_diagram} (T : ssyt μ) {i j val: ℕ} :
  T.rbc i val = j ↔
  ((i, j) ∉ μ ∨ val < T i j) ∧ (∀ j' < j, (i, j') ∈ μ ∧ T i j' ≤ val) :=
begin
  convert nat.find_eq_iff (T.rbc_aux i val), push_neg, refl,
end

lemma ssyt.rbc_eq_of_eq_row 
  {μ ν : young_diagram} (T : ssyt μ) (T' : ssyt ν) {i val : ℕ}
  (eq_cell : ∀ {j}, (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_row : ∀ {j}, T i j = T' i j) :
  T.rbc i val = T'.rbc i val :=
begin
  rw T.rbc_eq_iff,
  -- change first statement
  rw [eq_cell, eq_row],
  -- change second statement
  simp_rw [eq_cell, eq_row],
  rw ← T'.rbc_eq_iff,
end

end row_bump_column

section row_bump_step

section rbs_cert

structure ssyt.rbs_cert {μ : young_diagram} (T : ssyt μ) :=
  (i val : ℕ)
  (cell_up : ∀ {i'} (hi' : i' < i), (i', T.rbc i val) ∈ μ)
  (up : ∀ {i'} (hi' : i' < i), T i' (T.rbc i val) < val)

def ssyt.rbs_start_cert {μ : young_diagram} (T : ssyt μ) (val : ℕ) : T.rbs_cert :=
{ i := 0,
  val := val,
  cell_up := λ _ h, false.rec _ $ nat.not_lt_zero _ h,
  up := λ _ h, false.rec _ $ nat.not_lt_zero _ h,
}

@[reducible]
def ssyt.rbs_cert.j {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) : ℕ :=
  T.rbc h.i h.val

@[reducible]
def ssyt.rbs_cert.out {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) : ℕ :=
  T h.i h.j

@[simps]
def ssyt.rbs_cert.legal_of_cert {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) : 
  T.legal :=
{ i := h.i,
  j := h.j,
  val := h.val,
  cell_up := h.cell_up,
  cell_left := λ j' hj', (T.lt_rbc_iff.mp hj').1,
  left := λ j' hj', (T.lt_rbc_iff.mp hj').2,
  right := λ j' hj' hcell',
    le_of_lt $ (T.rbc_le_iff.mp (le_of_lt hj')).resolve_left (λ h, h hcell'),
  up := h.up,
  down := λ i' hi' hcell', begin
    apply ((T.rbc_not_cell_or_val_lt h.i h.val).resolve_left _).trans,
    exact T.col_strict hi' hcell',
    rw not_not, exact μ.nw_of (le_of_lt hi') (by refl) hcell',
  end,
}

@[simps]
def ssyt.rbs_cert.copy {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  {ν : young_diagram} (T' : ssyt ν)
  (eq_cell : ∀ i j (hi : i ≤ h.i), (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_le_row : ∀ i j (hi : i ≤ h.i), T i j = T' i j) : T'.rbs_cert :=
{ i := h.i,
  val := h.val,
  cell_up := λ i' hi', begin
    rw [← eq_cell _ _ (le_of_lt hi'),
        ← T.rbc_eq_of_eq_row T' 
          (λ j, eq_cell _ _ (le_refl _)) (λ j, eq_le_row _ _ (le_refl _))],
    exact h.cell_up hi',
  end,
  up := λ i' hi', begin
    rw [← eq_le_row _ _ (le_of_lt hi'),
        ← T.rbc_eq_of_eq_row T' 
          (λ j, eq_cell _ _ (le_refl _)) (λ j, eq_le_row _ _ (le_refl _))],
    exact h.up hi',
  end,
}

lemma ssyt.rbs_cert.copy_j {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  {ν : young_diagram} (T' : ssyt ν)
  (eq_cell : ∀ i j (hi : i ≤ h.i), (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_le_row : ∀ i j (hi : i ≤ h.i), T i j = T' i j) :
  (h.copy T' eq_cell eq_le_row).j = h.j :=
begin
  apply ssyt.rbc_eq_of_eq_row,
  intro j, rw eq_cell, refl,
  intro j, rw eq_le_row, refl
end

lemma ssyt.rbs_cert.copy_out {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  {ν : young_diagram} (T' : ssyt ν)
  (eq_cell : ∀ i j (hi : i ≤ h.i), (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_le_row : ∀ i j (hi : i ≤ h.i), T i j = T' i j) :
  (h.copy T' eq_cell eq_le_row).out = h.out :=
begin
  rw [ssyt.rbs_cert.out, ssyt.rbs_cert.out],
  rw ssyt.rbs_cert.copy_j,
  rw eq_le_row; refl
end

@[simps]
def ssyt.rbs_cert.copy' {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  {ν : young_diagram} (T' : ssyt ν)
  (subset_cell_lt_row : ∀ i j (hi : i < h.i), (i, j) ∈ μ → (i, j) ∈ ν)
  (eq_cell_row : ∀ j, (h.i, j) ∈ μ ↔ (h.i, j) ∈ ν)
  (le_lt_row : ∀ i j (hi : i < h.i), T' i j ≤ T i j)
  (eq_eq_row : ∀ j, T h.i j = T' h.i j) : T'.rbs_cert :=
{ i := h.i,
  val := h.val,
  cell_up := λ i' hi', begin
    apply subset_cell_lt_row _ _ hi',
    rw [← T.rbc_eq_of_eq_row T' eq_cell_row eq_eq_row],
    exact h.cell_up hi',
  end,
  up := λ i' hi', begin
    apply lt_of_le_of_lt (le_lt_row _ _ hi'),
    rw [← T.rbc_eq_of_eq_row T' eq_cell_row eq_eq_row],
    exact h.up hi',
  end,
}

lemma ssyt.rbs_cert.copy'_j {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  {ν : young_diagram} (T' : ssyt ν)
  (subset_cell_lt_row : ∀ i j (hi : i < h.i), (i, j) ∈ μ → (i, j) ∈ ν)
  (eq_cell_row : ∀ j, (h.i, j) ∈ μ ↔ (h.i, j) ∈ ν)
  (le_lt_row : ∀ i j (hi : i < h.i), T' i j ≤ T i j)
  (eq_eq_row : ∀ j, T h.i j = T' h.i j) :
(h.copy' T' subset_cell_lt_row eq_cell_row le_lt_row eq_eq_row).j = h.j :=
begin
  symmetry, apply ssyt.rbc_eq_of_eq_row,
  intro j, rw eq_cell_row,
  intro j, rw eq_eq_row,
end

lemma ssyt.rbs_cert.copy'_out {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  {ν : young_diagram} (T' : ssyt ν)
  (subset_cell_lt_row : ∀ i j (hi : i < h.i), (i, j) ∈ μ → (i, j) ∈ ν)
  (eq_cell_row : ∀ j, (h.i, j) ∈ μ ↔ (h.i, j) ∈ ν)
  (le_lt_row : ∀ i j (hi : i < h.i), T' i j ≤ T i j)
  (eq_eq_row : ∀ j, T h.i j = T' h.i j) :
(h.copy' T' subset_cell_lt_row eq_cell_row le_lt_row eq_eq_row).out = h.out :=
begin
  rw [ssyt.rbs_cert.out, ssyt.rbs_cert.out],
  rw ssyt.rbs_cert.copy'_j,
  rw eq_eq_row; refl
end

end rbs_cert

section rbs

def ssyt.rbs_cert.rbs {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (cell : (h.i, h.j) ∈ μ) : ssyt μ := h.legal_of_cert.replace cell

def ssyt.rbs_cert.rbs_end {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (not_cell : (h.i, h.j) ∉ μ) := h.legal_of_cert.add not_cell

@[reducible]
def ssyt.rbs_cert.rbs_end_corner {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (not_cell : (h.i, h.j) ∉ μ) : μ.outer_corner := (h.legal_of_cert.to_outer not_cell)
@[reducible]
def ssyt.rbs_cert.rbs_end_shape {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (not_cell : (h.i, h.j) ∉ μ) : young_diagram := (h.rbs_end_corner not_cell).add

lemma ssyt.rbs_cert.rbs_end_shape_eq_of_ne_row {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (not_cell : (h.i, h.j) ∉ μ) {i j : ℕ} (h_ne : i ≠ h.i) :
(i, j) ∈ h.rbs_end_shape not_cell ↔ (i, j) ∈ μ := 
begin
  rw young_diagram.outer_corner.mem_add,
  apply or_iff_right,
  rw prod.mk.inj_iff, exact λ h_eq, h_ne h_eq.1,
end

lemma ssyt.rbs_cert.rbs_entry {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (cell : (h.i, h.j) ∈ μ) {i j : ℕ} :
h.rbs cell i j = ite ((i, j) = (h.i, h.j)) h.val (T i j) := rfl

lemma ssyt.rbs_cert.rbs_end_entry {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (not_cell : (h.i, h.j) ∉ μ) {i j : ℕ} :
h.rbs_end not_cell i j = ite ((i, j) = (h.i, h.j)) h.val (T i j) := rfl

lemma ssyt.rbs_cert.rbs_entry_eq_of_ne_row {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) {i j : ℕ} (h_ne : i ≠ h.i) :
h.rbs cell i j = T i j := 
begin
  rw [h.rbs_entry, if_neg], rintro ⟨⟩, exact h_ne rfl
end

lemma ssyt.rbs_cert.rbs_end_entry_eq_of_ne_row {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (not_cell : (h.i, h.j) ∉ μ) {i j : ℕ} (h_ne : i ≠ h.i) :
h.rbs_end not_cell i j = T i j := 
begin
  rw [h.rbs_end_entry, if_neg], rintro ⟨rfl, _⟩, exact h_ne rfl
end

lemma ssyt.rbs_cert.rbs_entry_le {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) {i j : ℕ} :
h.rbs cell i j ≤ T i j := 
begin
  rw h.rbs_entry, split_ifs,
  cases h_1,
  exact le_of_lt ((T.rbc_not_cell_or_val_lt _ _).resolve_left (λ h, h cell)),
  refl
end

lemma ssyt.rbs_cert.next_rbc_le {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) :
 (h.rbs cell).rbc h.i.succ h.out ≤ h.j :=
begin
  rw [ssyt.rbc_le_iff, or_iff_not_imp_left], push_neg,
  intro cell',
  rw [h.rbs_entry_eq_of_ne_row _ (nat.succ_ne_self _)],
  apply T.col_strict (lt_add_one _) cell',
end

lemma ssyt.rbs_cert.next_cert_cell_up {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) :
let j' := (h.rbs cell).rbc h.i.succ h.out in
∀ i' (hi' : i' < h.i.succ), (i', j') ∈ μ :=
begin
  intros j' i' hi',
  rw nat.lt_succ_iff at hi',
  apply μ.nw_of hi' (h.next_rbc_le _) cell,
end

lemma ssyt.rbs_cert.next_cert_up {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) :
let j' := (h.rbs cell).rbc h.i.succ h.out in
∀ i' (hi' : i' < h.i.succ), (h.rbs cell) i' j' < h.out :=
begin
  intros j' i' hi',
  rw nat.lt_succ_iff at hi',
  rw h.rbs_entry,
  split_ifs,
  { exact (T.rbc_not_cell_or_val_lt _ _).resolve_left (λ h, h cell) },
    cases lt_or_eq_of_le hi',
    { apply lt_of_lt_of_le (T.col_strict h_2 _) 
            (T.row_weak' (h.next_rbc_le cell) cell),
      exact μ.nw_of (le_refl _) (h.next_rbc_le cell) cell },
    { subst i', rw [prod.mk.inj_iff, eq_self_iff_true, true_and] at h_1,
      apply @lt_of_le_of_lt _ _ _ h.val _,
      apply (T.lt_rbc_iff.mp _).2,
      exact lt_of_le_of_ne (h.next_rbc_le cell) h_1,
      exact (T.rbc_not_cell_or_val_lt _ _).resolve_left (λ h, h cell) }
end

@[simps]
def ssyt.rbs_cert.next_cert {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) : (h.rbs cell).rbs_cert :=
{ i := h.i.succ,
  val := h.out,
  cell_up := h.next_cert_cell_up cell,
  up := h.next_cert_up cell,
}

-- if we bump in an equal or larger value into the same row,
-- the resulting column is strictly further to the right
lemma ssyt.rbs_cert.rbc_lt_rbc {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ)
  {val' : ℕ} (hval : h.val ≤ val') :
h.j < (h.rbs cell).rbc h.i val' :=
begin
  rw ssyt.lt_rbc_iff, split, exact cell,
  rw [h.rbs_entry, if_pos rfl], exact hval,
end

-- if we bump in an equal or larger value into the same row,
-- the resulting output entry is weakly larger
lemma ssyt.rbs_cert.rbc_out_le_rbc_out {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ)
  {val' : ℕ} (hval : h.val ≤ val') 
  (cell' : (h.i, (h.rbs cell).rbc h.i val') ∈ μ) :
h.out ≤ (h.rbs cell) h.i ((h.rbs cell).rbc h.i val') :=
begin
  rw [ssyt.rbs_cert.out, h.rbs_entry, if_neg],
  exact T.row_weak (h.rbc_lt_rbc cell hval) cell',
  rw [prod.mk.inj_iff, eq_self_iff_true, true_and],
  exact ne_of_gt (h.rbc_lt_rbc cell hval),
end

end rbs

section size_wt

lemma ssyt.rbs_cert.rbs_end_size {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (not_cell : (h.i, h.j) ∉ μ) : 
  (h.legal_of_cert.to_outer not_cell).add.size = μ.size + 1 :=
by apply young_diagram.outer_corner.add_size

lemma ssyt.rbs_cert.rbs_wt {μ : young_diagram} (T : ssyt μ) (val : ℕ)
  (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) :
  (h.rbs cell).wt val + ite (val = T h.i h.j) 1 0 =
  T.wt val + ite (val = h.val) 1 0 :=
by apply ssyt.wt_replace

lemma ssyt.rbs_cert.rbs_end_wt {μ : young_diagram} (T : ssyt μ) (val : ℕ)
  (h : T.rbs_cert) (not_cell : (h.i, h.j) ∉ μ) :
  (h.rbs_end not_cell).wt val = T.wt val + ite (val = h.val) 1 0 :=
by apply ssyt.wt_add

end size_wt

end row_bump_step

section commutativity

/-
Commutativity:

T  →h1  T1
↓h      ↓h'
T' →h1' Tf

gives the same result, assuming the bumps are in different rows.
-/
lemma ssyt.rbs_cert.rbs_comm {μ : young_diagram}
  {T : ssyt μ} (h h1 : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) (cell1 : (h1.i, h1.j) ∈ μ)
  (h_h1_i : h1.i ≠ h.i)
  (h' : (h1.rbs cell1).rbs_cert) (hi : h'.i = h.i) (hval : h'.val = h.val)
  (h1' : (h.rbs cell).rbs_cert) (h1i : h1'.i = h1.i) (h1val : h1'.val = h1.val)
  (cell' : (h'.i, h'.j) ∈ μ := by {
    rwa [hi, (_ : h'.j = h.j)],
    rw [ssyt.rbs_cert.j, hi, hval, ssyt.rbc_eq_of_eq_row],
    exact λ _, iff.rfl,
    intro j, rw h1.rbs_entry_eq_of_ne_row, exact h_h1_i.symm }) 
  (cell1' : (h1'.i, h1'.j) ∈ μ := by {
    rwa [h1i, (_ : h1'.j = h1.j)],
    rw [ssyt.rbs_cert.j, h1i, h1val, ssyt.rbc_eq_of_eq_row],
    exact λ _, iff.rfl,
    intro j, rw h.rbs_entry_eq_of_ne_row, exact h_h1_i })
  (i j : ℕ) : h1'.rbs cell1' i j = h'.rbs cell' i j :=
begin
  have hj : h'.j = h.j := by {
    rw [ssyt.rbs_cert.j, hi, hval, ssyt.rbc_eq_of_eq_row],
    exact λ _, iff.rfl,
    intro j, rw h1.rbs_entry_eq_of_ne_row, exact h_h1_i.symm },
  have h1j : h1'.j = h1.j := by {
    rw [ssyt.rbs_cert.j, h1i, h1val, ssyt.rbc_eq_of_eq_row],
    exact λ _, iff.rfl,
    intro j, rw h.rbs_entry_eq_of_ne_row, exact h_h1_i },
  cases ne_or_eq i h.i,
    rw h'.rbs_entry_eq_of_ne_row,
    rw [h1'.rbs_entry, h1i, h1val, h1j, h.rbs_entry_eq_of_ne_row], refl,
    exact h_1, rwa hi,
  cases h_1,
    rw h1'.rbs_entry_eq_of_ne_row,
    rw [h'.rbs_entry, hi, hval, hj, h1.rbs_entry_eq_of_ne_row], refl,
    exact h_h1_i.symm, rw h1i, exact h_h1_i.symm,
end

end commutativity

section examples

-- #eval (μ5331.lowest_ssyt.rbs_start_cert 0).rbs sorry
-- #eval (μ5331.lowest_ssyt.rbs_start_cert 2).rbs sorry
-- #eval (μ5331.lowest_ssyt.rbs_start_cert 4).rbs_end sorry

end examples