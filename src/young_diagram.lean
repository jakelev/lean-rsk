import tactic
import data.set.basic

section young_diagram

@[ext]
structure young_diagram :=
  (cells : finset (ℕ × ℕ))
  (nw_of' : ∀ {i1 i2 j1 j2}, 
    i1 ≤ i2 → j1 ≤ j2 → (i2, j2) ∈ cells → (i1, j1) ∈ cells)

instance young_diagram.has_mem : has_mem (ℕ × ℕ) young_diagram :=
{ mem := λ c μ, c ∈ μ.cells, }
def young_diagram.nw_of (μ : young_diagram) 
  {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) : 
  (i1, j1) ∈ μ := μ.nw_of' hi hj hcell
-- def young_diagram.nw_of_c (μ : young_diagram) {c c' : ℕ × ℕ} 
--   (hi : c.fst ≤ c'.fst) (hj : c.snd ≤ c'.snd) (hcell : c' ∈ μ) : c ∈ μ :=
-- by { cases c, cases c', apply μ.nw_of hi hj hcell, }
instance young_diagram.has_subset : has_subset young_diagram :=
{ subset := λ μ ν, μ.cells ⊆ ν.cells }
instance young_diagram.has_emptyc : has_emptyc young_diagram :=
{ emptyc := { cells := finset.empty, nw_of' := λ _ _ _ _ _ _ h, h, } }

def μ_empty := (∅ : young_diagram)

def young_diagram.row (μ : young_diagram) (i : ℕ) := μ.cells.filter (λ c, c.fst = i)
def young_diagram.col (μ : young_diagram) (j : ℕ) := μ.cells.filter (λ c, c.snd = j)
def young_diagram.row_len (μ : young_diagram) (i : ℕ) := (μ.row i).card
def young_diagram.col_len (μ : young_diagram) (j : ℕ) := (μ.col j).card
def young_diagram.size (μ : young_diagram) := μ.cells.card
def young_diagram.row_lens (μ : young_diagram) : list ℕ := 
  list.map μ.row_len (list.range (μ.col_len 0))
def young_diagram.col_lens (μ : young_diagram) : list ℕ := 
  list.map μ.col_len (list.range (μ.row_len 0))

lemma young_diagram.row_def (μ : young_diagram) {i : ℕ} :
  μ.row i = μ.cells.filter (λ c, c.fst = i) := rfl

lemma young_diagram.mem_row_iff (μ : young_diagram) {i : ℕ} (c : ℕ × ℕ) :
  c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i :=
begin
  rw [young_diagram.row_def, finset.mem_filter], refl,
end

lemma young_diagram.row_def' (μ : young_diagram) (i : ℕ) : 
  μ.row i = finset.product {i} (finset.range (μ.row_len i)) :=
begin
  by_cases (μ.row i).nonempty, rotate,
  { rw finset.not_nonempty_iff_eq_empty at h,
    rw [young_diagram.row_len, h, 
      finset.card_empty, finset.range_zero, finset.product_empty], },

  have key : ∀ b : ℕ, (i, b) ∈ μ → 
    finset.product {i} (finset.range b.succ) ⊆ μ.row i,
  { rintros b hb ⟨i', j'⟩ h',
    rw [finset.mem_product, finset.mem_singleton, finset.mem_range] at h',
    change i' = _ ∧ j' < _ at h', obtain ⟨hi, hj⟩ := h', subst i',
    rw young_diagram.mem_row_iff,
    exact ⟨μ.nw_of (le_refl i) (nat.lt_succ_iff.mp hj) hb, rfl⟩, },
  
  { have key' : ∀ j, j ∈ (μ.row i).image prod.snd ↔ (i, j) ∈ μ,
    { intro j, rw finset.mem_image,
      split, rintro ⟨⟨a, b⟩, h, h'⟩,
      rw young_diagram.mem_row_iff at h, obtain ⟨hj', _ : a = i⟩ := h, subst a,
      change b = _ at h', subst b, exact hj',
      intro h, use (i, j), rw young_diagram.mem_row_iff,
      exact ⟨⟨h, rfl⟩, rfl⟩, },

    set j := ((μ.row i).image prod.snd).max' (h.image _) with hj,

    have : μ.row i = finset.product {i} (finset.range j.succ),
    { apply subset_antisymm,
      rotate, apply key, rw ← key', apply finset.max'_mem,
      rintro ⟨a, b⟩ hab,
      rw young_diagram.mem_row_iff at hab, 
      obtain ⟨hab, _ : a = i⟩ := hab, subst a,
      rw [finset.mem_product, finset.mem_singleton, finset.mem_range],
      split, refl, rw nat.lt_succ_iff, 
      apply finset.le_max', rw key', exact hab, },
    
    rw this, congr, rw young_diagram.row_len, rw this,
    rw [finset.card_product, finset.card_singleton, one_mul, finset.card_range],
  },
end

lemma young_diagram.mem_row_iff' (μ : young_diagram) (i j : ℕ) :
  (i, j) ∈ μ ↔ j < μ.row_len i :=
begin
  rw (_ : (i, j) ∈ μ ↔ (i, j) ∈ μ.row i),
  rw young_diagram.row_def',
  rw [finset.mem_product, finset.mem_singleton, finset.mem_range],
  rw and_iff_right, refl,
  rw [young_diagram.row_def, finset.mem_filter, and_iff_left rfl], refl,
end

-- lemma young_diagram.row_not_cell (μ : young_diagram) (i : ℕ) : (i, μ.row_len i) ∉ μ :=
-- begin
--   by_contra, apply @nat.not_succ_le_self (μ.row_len i),
--   suffices : finset.product {i} (finset.range (μ.row_len i).succ) ⊆ μ.row i,
--     convert finset.card_le_of_subset this,
--     rw [finset.card_product, finset.card_singleton, one_mul, finset.card_range],
--   rintros ⟨a, b⟩ hab, 
--   rw [finset.mem_product, finset.mem_singleton, finset.mem_range,
--       nat.lt_succ_iff] at hab,
--   change a = _ ∧ b ≤ _ at hab, obtain ⟨ha, hb⟩ := hab, subst a,
--   rw [young_diagram.row_def, finset.mem_filter],
--   exact ⟨μ.nw_of (le_refl _) hb h, rfl⟩,
-- end

-- lemma young_diagram.cell_of_lt_row_len (μ : young_diagram) (i j : ℕ) :
--   j < μ.row_len i → (i, j) ∈ μ :=
-- begin
--   by_contra, push_neg at h,
--   rw ← lt_self_iff_false (μ.row_len i),
--   suffices : μ.row i ⊂ finset.product {i} (finset.range (μ.row_len i)),
--     convert finset.card_lt_card this,
--     rw [finset.card_product, finset.card_singleton, one_mul, finset.card_range],
--   split,
--   { rintros ⟨a, b⟩ hab,
--     rw [finset.mem_product, finset.mem_singleton, finset.mem_range],
--     rw [young_diagram.row_def, finset.mem_filter] at hab,
--     split, exact hab.2,
--    },
-- end

-- lemma young_diagram.mem_row_iff (μ : young_diagram) (c : ℕ × ℕ) :
--   c ∈ μ ↔ c.snd < μ.row_len c.fst :=
-- begin
--   cases c with i j,
--   split; intro h,
--   { by_contra h_le, push_neg at h_le,
--     exact μ.row_not_cell i (μ.nw_of (le_refl _) h_le h), },
--   { 

--   },
--   -- rw (_ : c ∈ μ ↔ c ∈ μ.row c.fst),
--   -- rotate, 
--   -- { unfold young_diagram.row, 
--   --   rw [finset.mem_filter, and_iff_left rfl], refl, },
--   -- by_cases h : μ.row c.fst = ∅,
--   -- { unfold young_diagram.row_len, 
--   --   rw [h, finset.card_empty, iff_false_intro (nat.not_lt_zero c.snd)], refl, },
--   -- rw ← finset.not_nonempty_iff_eq_empty at h, push_neg at h,
  
-- end
-- lemma young_diagram.row_len_def' (μ : young_diagram) {i : ℕ} :
-- lemma young_diagram.row_def' (μ : young_diagram) (i : ℕ) :
--   μ.row i = ({i} : finset ℕ).product (finset.range (μ.row_len i)) :=
-- begin
--   ext ⟨a, b⟩,
--   rw [μ.row_def, finset.mem_filter, finset.mem_product, finset.mem_range,
--       finset.mem_singleton],
--   change ((a, b) ∈ μ ∧ a = i) ↔ (a = i ∧ b < _),
--   split; rintro ⟨h, h'⟩; subst a,
--   split, refl, unfold young_diagram.row_len,
-- end

-- lemma young_diagram.mem_row_iff (μ : young_diagram) (c : ℕ × ℕ) :
--   c ∈ μ ↔ c.snd < μ.row_len c.fst :=
-- begin
--   unfold young_diagram.row_len,
--   -- rw (_ : μ.row c.fst = finset.range (μ.row_len c.fst)),
--   rw (_ : c ∈ μ ↔ c ∈ μ.row c.fst),

--   sorry,
--   unfold young_diagram.row, 
--   rw [finset.mem_filter, and_iff_left rfl], refl,
-- end

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
  unfold list_decr, rw list_decr_iff, dsimp,
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
def young_diagram.cells_of_row_lens (w :list ℕ) : finset (ℕ × ℕ) :=
  finset.bUnion 
    (finset.range w.length)
    (λ i, ({i} : finset ℕ).product (finset.range (w.inth i)))

lemma young_diagram.cells_of_row_lens_mem (w : list ℕ) (c : ℕ × ℕ):
  c ∈ young_diagram.cells_of_row_lens w ↔ c.snd < w.inth c.fst :=
begin
  unfold young_diagram.cells_of_row_lens,
  rw finset.mem_bUnion, dsimp,
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

-- def young_diagram.cells_of_row_lens : list ℕ → finset (ℕ × ℕ)
-- | [] := finset.empty
-- | (x :: xs) := 
--   (({0} : finset ℕ).product (finset.range x)) ∪
--   finset.map
--     (function.embedding.prod_map 
--       ⟨nat.succ, by apply nat.succ.inj⟩
--       (function.embedding.refl ℕ))
--   (young_diagram.cells_of_row_lens xs)

-- lemma young_diagram.cells_of_row_lens_mem (w : list ℕ) (c : ℕ × ℕ):
--   c ∈ young_diagram.cells_of_row_lens w ↔ c.snd < w.inth c.fst :=
-- begin 
--   cases w with x xs,
--     exact (false_iff _).mpr (nat.not_lt_zero _),
--   cases c with i j,
--   cases i,
--   { change (0, j) ∈ _ ∪ _ ↔ j < x, 
--     rw finset.mem_union,

--   },

-- end
-- | [] c := (false_iff _).mpr (nat.not_lt_zero _)
-- | (x :: xs) (0, j) := begin
--   change _ ↔ j < x,
--   split; intro h,
--   { replace h := (finset.mem_union.mp h),

--    },
-- end
-- | (x :: xs) (nat.succ i, j) := sorry

def young_diagram.of_row_lens (r : list ℕ) (h : list_decr r) : young_diagram :=
{ cells := young_diagram.cells_of_row_lens r,
  nw_of' := λ i1 i2 j1 j2 hi hj hcell, begin
    rw young_diagram.cells_of_row_lens_mem at *,
    change j1 < r.inth i1, change j2 < r.inth i2 at hcell,
    apply lt_of_le_of_lt hj,
    apply lt_of_lt_of_le hcell,
    apply list_decr_iff.mp h, exact hi,
  end,}

end of_row_lens

section repr

def young_diagram.repr (μ : young_diagram) : string := μ.row_lens.to_string
def young_diagram.repr' (μ : young_diagram) : string :=
  string.intercalate "\n"
    (μ.repr :: (list.map (λ i : ℕ, string.join (list.repeat "□" i)) μ.row_lens))
instance young_diagram.has_repr : has_repr young_diagram :=
{ repr := young_diagram.repr' }

end repr

section corners

structure young_diagram.inner_corner (μ : young_diagram) :=
  (i j : ℕ)
  (cell : (i, j) ∈ μ)
  (row_right : ∀ {j'}, j < j' → (i, j') ∉ μ)
  (col_down : ∀ {i'}, i < i' → (i', j) ∉ μ)

structure young_diagram.outer_corner (μ : young_diagram) :=
  (i j : ℕ)
  (not_cell : (i, j) ∉ μ)
  (row_left : ∀ {j'}, j' < j → (i, j') ∈ μ)
  (col_up : ∀ {i'}, i' < i → (i', j) ∈ μ)

def young_diagram.inner_corner.del {μ : young_diagram} (c : μ.inner_corner) : 
young_diagram :=
{ cells := finset.erase μ.cells (c.i, c.j),
  nw_of' := λ i1 i2 j1 j2 hi hj hcell, begin
    rw finset.mem_erase at *,
    split,
    intro h, rw prod.mk.inj_iff at h, cases h, subst i1, subst j1,
    cases lt_or_eq_of_le hi,
      exact c.col_down h (μ.nw_of (le_refl _) hj hcell.2),
    cases lt_or_eq_of_le hj,
      exact c.row_right h_1 (μ.nw_of hi (le_refl _) hcell.2),
    apply hcell.1, subst i2, subst j2,
    exact μ.nw_of hi hj hcell.2,
  end
}

def young_diagram.outer_corner.out {μ : young_diagram} (c : μ.outer_corner) : 
young_diagram :=
{ cells := insert (c.i, c.j) μ.cells,
  nw_of' := λ i1 i2 j1 j2 hi hj hcell, begin
    rw finset.mem_insert at *,
    cases hcell,
    rw prod.mk.inj_iff at hcell, cases hcell, subst i2, subst j2,
    cases lt_or_eq_of_le hi,
      right, exact μ.nw_of (le_refl _) hj (c.col_up h),
    cases lt_or_eq_of_le hj,
      right, exact μ.nw_of hi (le_refl _) (c.row_left h_1),
    left, subst i1, subst j1,
    exact or.inr (μ.nw_of hi hj hcell),
  end,
}

end corners

@[simp]
def μ5331 : young_diagram := 
  young_diagram.of_row_lens [5, 3, 3, 1] (by {unfold list_decr, dec_trivial})



end young_diagram
