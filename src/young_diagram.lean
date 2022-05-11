import tactic
import data.set.basic

section young_diagram

@[ext]
structure young_diagram :=
  (cells : finset (ℕ × ℕ))
  (nw_of' : ∀ {i1 i2 j1 j2 : ℕ}, 
    i1 ≤ i2 → j1 ≤ j2 → (i2, j2) ∈ cells → (i1, j1) ∈ cells)

instance young_diagram.has_mem : has_mem (ℕ × ℕ) young_diagram :=
{ mem := λ c μ, c ∈ μ.cells, }

lemma young_diagram.mem_cells (μ : young_diagram) (c : ℕ × ℕ) :
  c ∈ μ.cells ↔ c ∈ μ := iff.rfl

def young_diagram.nw_of (μ : young_diagram) 
  {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) : 
  (i1, j1) ∈ μ := μ.nw_of' hi hj hcell

instance young_diagram.has_subset : has_subset young_diagram :=
{ subset := λ μ ν, μ.cells ⊆ ν.cells }

def young_diagram.size (μ : young_diagram) := μ.cells.card
def young_diagram.row (μ : young_diagram) (i : ℕ) := μ.cells.filter (λ c, c.fst = i)
def young_diagram.col (μ : young_diagram) (j : ℕ) := μ.cells.filter (λ c, c.snd = j)

lemma young_diagram.row_def (μ : young_diagram) {i : ℕ} :
  μ.row i = μ.cells.filter (λ c, c.fst = i) := rfl
lemma young_diagram.col_def (μ : young_diagram) {j : ℕ} :
  μ.col j = μ.cells.filter (λ c, c.snd = j) := rfl

lemma young_diagram.mem_row_iff (μ : young_diagram) {i : ℕ} (c : ℕ × ℕ) :
  c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i :=
by {rw [young_diagram.row_def, finset.mem_filter], refl}
lemma young_diagram.mem_col_iff (μ : young_diagram) {j : ℕ} (c : ℕ × ℕ) :
  c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j :=
by {rw [young_diagram.col_def, finset.mem_filter], refl}

lemma young_diagram.mem_iff_mem_row (μ : young_diagram) {i j : ℕ} :
  (i, j) ∈ μ ↔ (i, j) ∈ μ.row i :=
by rw [young_diagram.mem_row_iff, and_iff_left rfl]
lemma young_diagram.mem_iff_mem_col (μ : young_diagram) {i j : ℕ} :
  (i, j) ∈ μ ↔ (i, j) ∈ μ.col j :=
by rw [young_diagram.mem_col_iff, and_iff_left rfl]

lemma young_diagram.row_len_aux (μ : young_diagram) (i : ℕ) : ∃ j, (i, j) ∉ μ := 
begin
  obtain ⟨j, hj⟩ := infinite.exists_not_mem_finset ((μ.row i).image prod.snd), 
  use j, intro hij, apply hj,
  rw finset.mem_image, rw μ.mem_iff_mem_row at hij,
  exact ⟨_, hij, rfl⟩,
end
lemma young_diagram.col_len_aux (μ : young_diagram) (j : ℕ) : ∃ i, (i, j) ∉ μ := 
begin
  obtain ⟨i, hi⟩ := infinite.exists_not_mem_finset ((μ.col j).image prod.fst), 
  use i, intro hij, apply hi,
  rw finset.mem_image, rw μ.mem_iff_mem_col at hij,
  exact ⟨_, hij, rfl⟩,
end

def young_diagram.row_len (μ : young_diagram) (i : ℕ) : ℕ := 
  nat.find $ μ.row_len_aux i
def young_diagram.col_len (μ : young_diagram) (j : ℕ) : ℕ := 
  nat.find $ μ.col_len_aux j
def young_diagram.row_lens (μ : young_diagram) : list ℕ := 
  list.map μ.row_len (list.range $ μ.col_len 0)
def young_diagram.col_lens (μ : young_diagram) : list ℕ := 
  list.map μ.col_len (list.range $ μ.row_len 0)

lemma young_diagram.row_len_def (μ : young_diagram) {i : ℕ} :
  μ.row_len i = nat.find (μ.row_len_aux i) := rfl
lemma young_diagram.col_len_def (μ : young_diagram) {j : ℕ} :
  μ.col_len j = nat.find (μ.col_len_aux j) := rfl

lemma young_diagram.mem_row_iff' (μ : young_diagram) {i j : ℕ} :
  (i, j) ∈ μ ↔ j < μ.row_len i :=
begin
  rw [μ.row_len_def, nat.lt_find_iff], push_neg,
  split; intro h,
  exact λ m hmj, μ.nw_of (le_refl i) hmj h,
  exact h _ (le_refl _),
end
lemma young_diagram.mem_col_iff' (μ : young_diagram) {i j : ℕ} :
  (i, j) ∈ μ ↔ i < μ.col_len j :=
begin
  rw [μ.col_len_def, nat.lt_find_iff], push_neg,
  split; intro h,
  exact λ m hmj, μ.nw_of hmj (le_refl j) h,
  exact h _ (le_refl _),
end

lemma young_diagram.row_eq_prod_range (μ : young_diagram) {i : ℕ} :
  μ.row i = finset.product {i} (finset.range $ μ.row_len i) :=
begin
  ext ⟨a, b⟩,
  rw [finset.mem_product, finset.mem_singleton, finset.mem_range,
      μ.mem_row_iff, μ.mem_row_iff',
      and_comm, and.congr_right_iff],
  rintro rfl, refl,
end
lemma young_diagram.col_eq_prod_range (μ : young_diagram) {j : ℕ} :
  μ.col j = finset.product (finset.range $ μ.col_len j) {j} :=
begin
  ext ⟨a, b⟩,
  rw [finset.mem_product, finset.mem_singleton, finset.mem_range,
      μ.mem_col_iff, μ.mem_col_iff', and.congr_left_iff],
  rintro rfl, refl,
end

lemma young_diagram.row_len_eq_card (μ : young_diagram) {i : ℕ} :
  μ.row_len i = (μ.row i).card :=
begin
  rw μ.row_eq_prod_range, 
  rw [finset.card_product, finset.card_singleton, finset.card_range, one_mul],
end
lemma young_diagram.col_len_eq_card (μ : young_diagram) {j: ℕ} :
  μ.col_len j = (μ.col j).card :=
begin
  rw μ.col_eq_prod_range,
  rw [finset.card_product, finset.card_singleton, finset.card_range, mul_one],
end

lemma young_diagram.row_len_decr (μ : young_diagram) {i1 i2 : ℕ} (hi : i1 ≤ i2) :
  μ.row_len i2 ≤ μ.row_len i1 :=
begin
  by_contra h_lt, push_neg at h_lt,
  have := μ.nw_of hi (le_refl _),
  rw [μ.mem_row_iff', μ.mem_row_iff'] at this,
  exact (lt_self_iff_false _).mp (this h_lt),
end

lemma young_diagram.col_len_decr (μ : young_diagram) {j1 j2 : ℕ} (hj : j1 ≤ j2) :
  μ.col_len j2 ≤ μ.col_len j1 :=
begin
  by_contra h_lt, push_neg at h_lt,
  have := μ.nw_of (le_refl _) hj,
  rw [μ.mem_col_iff', μ.mem_col_iff'] at this,
  exact (lt_self_iff_false _).mp (this h_lt),
end

section μ_empty

instance young_diagram.has_emptyc : has_emptyc young_diagram :=
{ emptyc := { cells := finset.empty, nw_of' := λ _ _ _ _ _ _ h, h, } }

def μ_empty := (∅ : young_diagram)

@[simp] lemma μ_empty_size : (∅ : young_diagram).size = 0 := rfl

end μ_empty

section of_row_lens

def list_decr : list ℕ → Prop
| [] := true
| [x] := true
| (x :: y :: xs) := y ≤ x ∧ list_decr (y :: xs)

lemma list_decr_iff : 
  Π {w : list ℕ},
  list_decr w ↔ ∀ n n', n ≤ n' → w.inth n' ≤ w.inth n
| [] := begin  apply (true_iff _).mpr, exact λ _ _ _, le_refl 0, end
| [x] := begin apply (true_iff _).mpr, intros n n' h,
               cases n', rw nat.le_zero_iff.mp h, exact nat.zero_le _, end
| (x :: y :: xs) := begin
  unfold list_decr, rw list_decr_iff, dsimp only [list.inth],
  split,
  { rintros ⟨h, h'⟩ n n' hn, 
    cases n', rw nat.le_zero_iff at hn, subst n,
    cases n, --change ((y :: xs).nth _).iget ≤ x,
    exact (h' 0 n' (nat.zero_le _)).trans h,
    apply h', exact nat.succ_le_succ_iff.mp hn, },
  { intro h', split,
    exact h' 0 1 (nat.zero_le _),
    intros n n' hn,
    exact h' n.succ n'.succ (nat.succ_le_succ hn), },
end

@[simp]
def young_diagram.cells_of_row_lens (w : list ℕ) : finset (ℕ × ℕ) :=
  finset.bUnion 
    (finset.range w.length)
    (λ i, ({i} : finset ℕ).product (finset.range $ w.inth i))

lemma young_diagram.mem_of_row_lens (w : list ℕ) (c : ℕ × ℕ):
  c ∈ young_diagram.cells_of_row_lens w ↔ c.snd < w.inth c.fst :=
begin
  unfold young_diagram.cells_of_row_lens,
  rw finset.mem_bUnion, dsimp only [list.inth],
  split; intro h,
  { obtain ⟨a, h, h'⟩ := h,
    rw finset.mem_product at h',
    obtain ⟨hc1, hc2⟩ := h',
    rw ← finset.eq_of_mem_singleton hc1 at hc2,
    exact finset.mem_range.mp hc2, },
  { use c.fst, 
    have : c.fst < w.length,
    { by_contra h', push_neg at h',
      apply nat.not_lt_zero c.snd, convert h,
      rw list.nth_eq_none_iff.mpr h', refl, },
    exact ⟨finset.mem_range.mpr this,
           finset.mem_product.mpr 
             ⟨finset.mem_singleton_self _, finset.mem_range.mpr h⟩⟩, },
end

def young_diagram.of_row_lens (r : list ℕ) (h : list_decr r) : young_diagram :=
{ cells := young_diagram.cells_of_row_lens r,
  nw_of' := λ i1 i2 j1 j2 hi hj hcell, begin
    rw young_diagram.mem_of_row_lens at *,
    change j1 < r.inth i1, change j2 < r.inth i2 at hcell,
    apply lt_of_le_of_lt hj,
    apply lt_of_lt_of_le hcell,
    apply list_decr_iff.mp h, exact hi,
  end,}

@[simp] lemma young_diagram.of_row_lens.mem (w : list ℕ) (h : list_decr w)
  {c : ℕ × ℕ} :
  c ∈ young_diagram.of_row_lens w h ↔ c.snd < w.inth c.fst :=
young_diagram.mem_of_row_lens w c

end of_row_lens

section repr

def young_diagram.repr (μ : young_diagram) : string := μ.row_lens.to_string
def young_diagram.repr' (μ : young_diagram) : string :=
  string.intercalate "\n" $
    μ.repr :: (list.map (λ i, string.join $ list.repeat "□" i) μ.row_lens)
instance young_diagram.has_repr : has_repr young_diagram :=
{ repr := young_diagram.repr' }

end repr

section corners

structure young_diagram.inner_corner (μ : young_diagram) :=
  (i j : ℕ)
  (cell : (i, j) ∈ μ)
  (cell_right : ∀ {j'}, j < j' → (i, j') ∉ μ)
  (cell_down : ∀ {i'}, i < i' → (i', j) ∉ μ)

structure young_diagram.outer_corner (μ : young_diagram) :=
  (i j : ℕ)
  (not_cell : (i, j) ∉ μ)
  (cell_left : ∀ {j'}, j' < j → (i, j') ∈ μ)
  (cell_up : ∀ {i'}, i' < i → (i', j) ∈ μ)

instance young_diagram.dec_cell_right (μ : young_diagram)
  (i j : ℕ) : decidable (∀ {j'}, j < j' → (i, j') ∉ μ) :=
if hj : j.succ < μ.row_len i
then is_false $ λ h', h' (lt_add_one j) (μ.mem_row_iff'.mpr hj)
else is_true $ λ j' h' hcell, hj (μ.mem_row_iff'.mp $ μ.nw_of (le_refl _) h' hcell)

instance young_diagram.dec_cell_down (μ : young_diagram)
  (i j : ℕ) : decidable (∀ {i'}, i < i' → (i', j) ∉ μ) :=
if hi : i.succ < μ.col_len j
then is_false $ λ h', h' (lt_add_one i) (μ.mem_col_iff'.mpr hi)
else is_true $ λ j' h' hcell, hi (μ.mem_col_iff'.mp $ μ.nw_of h' (le_refl _) hcell)

-- presumably easier because they only involve finitely-many values of j'
instance young_diagram.dec_cell_left (μ : young_diagram)
  (i j : ℕ) : decidable (∀ {j'}, j' < j → (i, j') ∈ μ) := by apply_instance
instance young_diagram.dec_cell_up (μ : young_diagram)
  (i j : ℕ) : decidable (∀ {i'}, i' < i → (i', j) ∈ μ) := by apply_instance


def young_diagram.inner_corner.del {μ : young_diagram} (c : μ.inner_corner) : 
young_diagram :=
{ cells := μ.cells.erase (c.i, c.j), -- finset.erase
  nw_of' := λ i1 i2 j1 j2 hi hj hcell, begin
    rw finset.mem_erase at *,
    split,
    intro h, cases h, clear h,
    cases lt_or_eq_of_le hi,
      exact c.cell_down h (μ.nw_of (le_refl _) hj hcell.2),
    cases lt_or_eq_of_le hj,
      exact c.cell_right h_1 (μ.nw_of hi (le_refl _) hcell.2),
    apply hcell.1, subst i2, subst j2,
    exact μ.nw_of hi hj hcell.2,
  end
}

lemma young_diagram.inner_corner.del_def 
  {μ : young_diagram} (c : μ.inner_corner) : 
c.del.cells = μ.cells.erase (c.i, c.j) := rfl

@[simp] lemma young_diagram.inner_corner.mem_del
  {μ : young_diagram} (c : μ.inner_corner) {i j : ℕ} : 
(i, j) ∈ c.del ↔ (i, j) ≠ (c.i, c.j) ∧ (i, j) ∈ μ := finset.mem_erase

lemma young_diagram.inner_corner.del_size
  {μ : young_diagram} (c : μ.inner_corner) : 
  c.del.size + 1 = μ.size := finset.card_erase_add_one c.cell

def young_diagram.outer_corner.add {μ : young_diagram} (c : μ.outer_corner) : 
young_diagram :=
{ cells := insert (c.i, c.j) μ.cells,
  nw_of' := λ i1 i2 j1 j2 hi hj hcell, begin
    rw finset.mem_insert at *,
    cases hcell,
    cases hcell,
    cases lt_or_eq_of_le hi,
      right, exact μ.nw_of (le_refl _) hj (c.cell_up h),
    cases lt_or_eq_of_le hj,
      right, exact μ.nw_of hi (le_refl _) (c.cell_left h_1),
    left, subst i1, subst j1,
    exact or.inr (μ.nw_of hi hj hcell),
  end
}

lemma young_diagram.outer_corner.add_def
  {μ : young_diagram} (c : μ.outer_corner) : 
c.add.cells = insert (c.i, c.j) μ.cells := rfl

@[simp] lemma young_diagram.outer_corner.mem_add
  {μ : young_diagram} (c : μ.outer_corner) {i j : ℕ} : 
(i, j) ∈ c.add ↔ (i, j) = (c.i, c.j) ∨ (i, j) ∈ μ := finset.mem_insert

lemma young_diagram.outer_corner.add_size
  {μ : young_diagram} (c : μ.outer_corner) : 
  c.add.size = μ.size + 1 := finset.card_insert_of_not_mem c.not_cell

def young_diagram.inner_corner.to_outer
  {μ : young_diagram} (c : μ.inner_corner) : c.del.outer_corner :=
{ i := c.i,
  j := c.j,
  not_cell := begin 
    rw young_diagram.inner_corner.mem_del,
    rw not_and', push_neg, exact λ _, rfl,
  end,
  cell_left := λ j' hj, begin
    rw young_diagram.inner_corner.mem_del,
    split, exact λ h, ne_of_lt hj (prod.ext_iff.mp h).2,
    exact μ.nw_of (le_refl _) (le_of_lt hj) c.cell,
  end,
  cell_up := λ i' hi, begin
    rw young_diagram.inner_corner.mem_del,
    split, exact λ h, ne_of_lt hi (prod.ext_iff.mp h).1,
    exact μ.nw_of (le_of_lt hi) (le_refl _) c.cell,
  end,
}

def young_diagram.outer_corner.to_inner 
  {μ : young_diagram} (c : μ.outer_corner) : c.add.inner_corner :=
{ i := c.i,
  j := c.j,
  cell := begin
    rw young_diagram.outer_corner.mem_add,
    left, refl,
  end,
  cell_right := λ j' hj, begin
    rw young_diagram.outer_corner.mem_add, intro h,
    cases h, exact (ne_of_lt hj).symm (prod.ext_iff.mp h).2,
    exact c.not_cell (μ.nw_of (le_refl _) (le_of_lt hj) h),
  end,
  cell_down := λ i' hi, begin
    rw young_diagram.outer_corner.mem_add, intro h,
    cases h, exact (ne_of_lt hi).symm (prod.ext_iff.mp h).1,
    exact c.not_cell (μ.nw_of (le_of_lt hi) (le_refl _) h),
  end,
}

@[simp] lemma young_diagram.outer_inner {μ : young_diagram} (c : μ.inner_corner) :
  c.to_outer.add = μ :=
begin
  ext ⟨i, j⟩,
  rw [c.to_outer.add.mem_cells, μ.mem_cells, c.to_outer.mem_add, c.mem_del],
  change (i, j) = (c.i, c.j) ∨ _ ↔ _,
  by_cases (i, j) = (c.i, c.j),
    rw [h, eq_self_iff_true, true_or, true_iff],
    exact c.cell,
  rw [or_iff_right h, and_iff_right h],
end

@[simp] lemma young_diagram.inner_outer {μ : young_diagram} (c : μ.outer_corner) :
  c.to_inner.del = μ :=
begin
  ext ⟨i, j⟩,
  rw [c.to_inner.del.mem_cells, μ.mem_cells, c.to_inner.mem_del, c.mem_add],
  change (i, j) ≠ (c.i, c.j) ∧ _ ↔ _,
  by_cases (i, j) = (c.i, c.j),
    rw [h, ← (false_iff _).mpr c.not_cell, iff_false],
    push_neg, exact λ h, false.rec _ (h rfl),
  rw [and_iff_right h, or_iff_right h],
end

end corners

section examples

@[simp]
def μ5331 : young_diagram := 
  young_diagram.of_row_lens [5, 3, 3, 1] (by {unfold list_decr, dec_trivial})

def μ5331.corner2 : μ5331.inner_corner :=
{ i := 2,
  j := 2,
  cell := dec_trivial,
  cell_right := 
  -- begin
  --   have : (2 : ℕ).succ < μ5331.row_len 2,
  --     rw young_diagram.row_len_eq_card,
  --     -- dec_trivial,
  --     sorry,
  --   sorry,
  -- end,
  λ j', begin
    contrapose!, dsimp only [μ5331], rw young_diagram.of_row_lens.mem,
    exact λ h, nat.lt_succ_iff.mp h,
  end,
  cell_down := λ i', begin
    dsimp only [μ5331], rw [young_diagram.of_row_lens.mem, list.inth],
    contrapose!, intro h,

    -- beginning of μ
    repeat { cases i', dec_trivial, simp only [list.nth] at h, },
    -- rest of μ
    exfalso, apply not_le_of_lt h, clear h,
    repeat { cases i', dec_trivial, simp only [list.nth], },
    -- empty list
    exact nat.zero_le _,
  end, }

def μ5331.corner3 : μ5331.outer_corner :=
{ i := 1,
  j := 3,
  not_cell := dec_trivial,
  cell_left := dec_trivial,
  -- λ j', begin
  --   contrapose!, dsimp, rw young_diagram.of_row_lens.mem,
  --   push_neg, exact id,
  -- end,
  cell_up := dec_trivial,
  -- λ i', begin
  --   dsimp, rw [young_diagram.of_row_lens.mem, list.inth],
  --   intro h, rw nat.lt_succ_iff at h,
  --   -- beginning of μ
  --   repeat { cases i', dec_trivial, 
  --            simp only [list.nth], 
  --            repeat { rw nat.succ_le_succ_iff at h },},
  --   -- empty list
  --   exfalso, apply nat.not_succ_le_zero _ h,
  -- end,
}

#eval μ5331

#eval μ5331.corner2.del

#eval μ5331.corner3.add

end examples

end young_diagram
