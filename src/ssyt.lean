import tactic
import young_diagram

section ssyt

@[ext]
structure ssyt (μ : young_diagram) :=
  (entry : ℕ → ℕ → ℕ)
  (row_weak : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → 
    entry i j1 ≤ entry i j2)
  (col_strict : ∀ {i1 i2 j: ℕ}, i1 < i2 → (i2, j) ∈ μ → 
    entry i1 j < entry i2 j)
  (zeros' : ∀ {i j}, (i, j) ∉ μ → entry i j = 0)

instance ssyt.to_fun {μ : young_diagram} : 
  has_coe_to_fun (ssyt μ) (λ T, ℕ → ℕ → ℕ) :=
{ coe := λ T i j, T.entry i j }

-- lemma ssyt.row_weak {μ : young_diagram} (T : ssyt μ)
--   {i j1 j2 : ℕ} (hj : j1 < j2) (hcell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
--   T.row_weak' hj hcell

-- lemma ssyt.col_strict {μ : young_diagram} (T : ssyt μ)
--   {i1 i2 j : ℕ} (hi : i1 < i2) (hcell : (i2, j) ∈ μ) : T i1 j < T i2 j :=
--   T.col_strict' hi hcell

lemma ssyt.zeros {μ : young_diagram} (T : ssyt μ) 
  {i j : ℕ} (not_cell : (i, j) ∉ μ) : T i j = 0 := T.zeros' not_cell

lemma ssyt.row_weak' {μ : young_diagram} (T : ssyt μ) {i j1 j2 : ℕ}
  (hj : j1 ≤ j2) (cell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
by {cases eq_or_lt_of_le hj, subst h, exact T.row_weak h cell}

lemma ssyt.col_weak {μ : young_diagram} (T : ssyt μ) {i1 i2 j : ℕ}
  (hi : i1 ≤ i2) (cell : (i2, j) ∈ μ) : T i1 j ≤ T i2 j :=
by {cases eq_or_lt_of_le hi, subst h, exact le_of_lt (T.col_strict h cell)}

def ssyt.to_fun_cells {μ : young_diagram} (T : ssyt μ) (cc : μ.cells) : ℕ :=
  T cc.val.1 cc.val.2

end ssyt

section ssyt_bounded

-- fintype instance for ssyts with bounded entries
-- method is to express as a subtype of (μ.cells → fin m)

def ssyt_bounded (μ : young_diagram) (m : ℕ) :=
  {T : ssyt μ // ∀ {i j}, (i, j) ∈ μ → T i j < m}

def ssyt'_bounded (μ : young_diagram) (m : ℕ) :=
  {entry : μ.cells → fin m //
   (∀ {c c' : μ.cells},
    c.val.1 = c'.val.1 → c.val.2 < c'.val.2 → entry c ≤ entry c')
   ∧ (∀ {c c' : μ.cells},
    c.val.1 < c'.val.1 → c.val.2 = c'.val.2 → entry c < entry c') }

def ssyt_bounded.to_ssyt'_bounded {μ : young_diagram} {m : ℕ}
  (TT : ssyt_bounded μ m) : ssyt'_bounded μ m :=
{ val := λ c, ⟨TT.val.to_fun_cells c, 
               begin apply TT.prop, convert c.prop, ext; refl, end⟩,
  property := ⟨
    λ c c' hi hj, begin
    cases c with c hc, cases c with i1 j1,
    cases c' with c' hc', cases c' with i2 j2,
    dsimp only at *, subst i2,
    apply TT.val.row_weak hj hc',
  end,
  λ c c' hi hj, begin
    cases c with c hc, cases c with i1 j1,
    cases c' with c' hc', cases c' with i2 j2,
    dsimp only at *, subst j2,
    apply TT.val.col_strict hi hc',
  end⟩
}

def ssyt'_bounded.to_ssyt_bounded {μ : young_diagram} {m : ℕ} 
  (T' : ssyt'_bounded μ m) : ssyt_bounded μ m :=
⟨{ entry := λ i j, dite ((i, j) ∈ μ) (λ h, T'.val ⟨(i, j), h⟩) (λ _, 0),
  row_weak := λ i j1 j2 hj hcell, begin
    split_ifs,
    apply T'.prop.1, refl, exact hj,
    apply nat.zero_le,
  end,
  col_strict := λ i1 i2 j hi hcell, begin
    rw [dif_pos hcell, dif_pos (μ.nw_of (le_of_lt hi) (le_refl j) hcell)],
    apply T'.prop.2, exact hi, refl,
  end,
  zeros' := λ i j h, dif_neg h
},
begin
  intros i j h, change dite _ _ _ < _, rw dif_pos h, 
  exact (T'.val _).prop,
end⟩

def ssyt.bounded_equiv (μ : young_diagram) (m : ℕ) : 
  ssyt_bounded μ m ≃ ssyt'_bounded μ m :=
{ to_fun := λ T, T.to_ssyt'_bounded,
  inv_fun := λ T', T'.to_ssyt_bounded,
  left_inv := λ T, begin
    ext i j,
    change dite _ _ _ = _, split_ifs,
    refl, exact (T.val.zeros' h).symm,
  end,
  right_inv := λ T', begin
    ext ⟨⟨i, j⟩, hcell⟩,
    change dite _ _ _ = _, rw dif_pos, refl,
  end,
}

instance ssyt'_bounded.fintype {μ : young_diagram} {m : ℕ} : 
  fintype (ssyt'_bounded μ m) := subtype.fintype _

instance ssyt_bounded.fintype {μ : young_diagram} {m : ℕ} : 
  fintype (ssyt_bounded μ m) := 
  fintype.of_equiv _ (ssyt.bounded_equiv μ m).symm

end ssyt_bounded

section legal_replace_add

structure ssyt.legal {μ : young_diagram} (T : ssyt μ) :=
  (i j val : ℕ)
  (cell_left : ∀ {j'}, j' < j → (i, j') ∈ μ)
  (cell_up : ∀ {i'}, i' < i → (i', j) ∈ μ)
  (left : ∀ {j'}, j' < j → T i j' ≤ val)
  (up : ∀ {i'}, i' < i → T i' j < val)
  (right : ∀ {j'}, j < j' → (i, j') ∈ μ → val ≤ T i j')  
  (down : ∀ {i'}, i < i' → (i', j) ∈ μ → val < T i' j)

def ssyt.legal.replace {μ : young_diagram} {T : ssyt μ}
  (h : T.legal) (cell : (h.i, h.j) ∈ μ) : ssyt μ :=
{ entry := λ i j, ite ((i, j) = (h.i, h.j)) h.val (T i j),
  row_weak := λ i j1 j2 hj cell, begin
    split_ifs,
    { refl },
    { cases h_1, apply h.right hj cell, },
    { cases h_2, apply h.left hj, },
    { exact T.row_weak hj cell }
  end,
  col_strict := λ i1 i2 j hi cell, begin
    split_ifs,
    { cases h_1, cases h_2, exact false.rec _ ((lt_self_iff_false _).mp hi) },
    { cases h_1, apply h.down hi cell },
    { cases h_2, apply h.up hi },
    { exact T.col_strict hi cell }
  end,
  zeros' := λ i j not_cell, begin
    rw [if_neg, T.zeros not_cell],
    exact λ h_eq, (h_eq ▸ not_cell) cell,
  end,
}

def ssyt.legal.to_outer {μ : young_diagram} {T : ssyt μ}
  (h : T.legal) (not_cell : (h.i, h.j) ∉ μ):
  μ.outer_corner :=
{ i := h.i,
  j := h.j,
  not_cell := not_cell,
  cell_left := h.cell_left,
  cell_up := h.cell_up }

def ssyt.legal.add {μ : young_diagram} {T : ssyt μ}
  (h : T.legal) (not_cell : (h.i, h.j) ∉ μ) : ssyt (h.to_outer not_cell).add :=
{ entry := λ i j, ite ((i, j) = (h.i, h.j)) h.val (T i j),
  row_weak := λ i j1 j2 hj cell, begin
    rw young_diagram.outer_corner.mem_add at cell,
    split_ifs,
    { refl },
    { cases h_1, cases cell, exact false.rec _ (h_2 cell),
      apply h.right hj cell },
    { cases h_2, apply h.left hj },
    { cases cell, exact false.rec _ (h_2 cell),
      exact T.row_weak hj cell }
  end,
  col_strict := λ i1 i2 j hi cell, begin
    rw young_diagram.outer_corner.mem_add at cell,
    split_ifs,
    { rw prod.mk.inj_iff at h_1, rw prod.mk.inj_iff at h_2,
      rw [h_1.1, h_2.1, lt_self_iff_false] at hi,
      exact false.rec _ hi },
    { cases h_1, cases cell, exact false.rec _ (h_2 cell),
      apply h.down hi cell },
    { cases h_2, apply h.up hi },
    { cases cell, exact false.rec _ (h_2 cell),
      exact T.col_strict hi cell }
  end,
  zeros' := λ i j not_cell, begin
    rw young_diagram.outer_corner.mem_add at not_cell, push_neg at not_cell,
    rw [if_neg, T.zeros not_cell.2], exact not_cell.1,
  end,
}

lemma ssyt.legal.entry_replace {μ : young_diagram} {T : ssyt μ}
  (h : T.legal) (cell : (h.i, h.j) ∈ μ) (i j : ℕ) :
  (h.replace cell) i j = ite ((i, j) = (h.i, h.j)) h.val (T i j) := rfl

lemma ssyt.legal.entry_add {μ : young_diagram} {T : ssyt μ}
  (h : T.legal) (not_cell : (h.i, h.j) ∉ μ) (i j : ℕ) :
  (h.add not_cell) i j = ite ((i, j) = (h.i, h.j)) h.val (T i j) := rfl

end legal_replace_add

section weight

def ssyt.strip {μ : young_diagram} (T : ssyt μ) (val : ℕ) : finset (ℕ × ℕ) :=
  μ.cells.filter (λ c, T c.fst c.snd = val)
@[simp] lemma ssyt.mem_strip {μ : young_diagram} (T : ssyt μ) {val i j : ℕ} :
  (i, j) ∈ T.strip val ↔ (i, j) ∈ μ ∧ T i j = val :=
by { rw [ssyt.strip, finset.mem_filter], refl }

def ssyt.wt {μ : young_diagram} (T : ssyt μ) (val : ℕ) : ℕ :=
  (T.strip val).card

lemma ssyt.strip_add {μ : young_diagram} (T : ssyt μ) (val : ℕ)
  (h : T.legal) (not_cell : (h.i, h.j) ∉ μ) :
  (h.add not_cell).strip val =
  ite (val = h.val) (insert (h.i, h.j) (T.strip val)) (T.strip val) :=
begin
  ext ⟨i, j⟩,
  rw [ssyt.mem_strip, young_diagram.outer_corner.mem_add, ssyt.legal.entry_add],
  split_ifs; try {rw finset.mem_insert}; rw ssyt.mem_strip,
  { cases h_1, cases h_2,
    simp only [not_cell, or_false, eq_self_iff_true, and_true, false_and, iff_true],
    refl, },
  { cases h_1, simp only [not_cell, ne.symm h_2, and_false, false_and] },
  { cases h_2, rw [or_iff_right, or_iff_right]; exact h_1 },
  { rw or_iff_right, exact h_1, }
end

lemma ssyt.wt_add {μ : young_diagram} (T : ssyt μ) (val : ℕ)
  (h : T.legal) (not_cell : (h.i, h.j) ∉ μ) :
  (h.add not_cell).wt val = T.wt val + ite (val = h.val) 1 0 :=
begin
  rw [ssyt.wt, ssyt.wt, ssyt.strip_add, apply_ite finset.card],
  split_ifs,
  { rw finset.card_insert_of_not_mem,
    rw ssyt.mem_strip,
    simp only [not_cell, false_and, not_false_iff] },
  { rw add_zero }
end

lemma ssyt.strip_replace {μ : young_diagram} (T : ssyt μ) (val : ℕ)
  (h : T.legal) (cell : (h.i, h.j) ∈ μ) :
  ite (val = T h.i h.j) 
    (insert (h.i, h.j) ((h.replace cell).strip val))
    ((h.replace cell).strip val) =
  ite (val = h.val) 
    (insert (h.i, h.j) (T.strip val)) 
    (T.strip val) :=
begin
  ext ⟨i, j⟩,
  split_ifs,
  all_goals {
    try { rw finset.mem_insert }, try { rw finset.mem_insert },
    rw [ssyt.mem_strip, ssyt.mem_strip, h.entry_replace],
  },
  { split_ifs, cases h_3,
    simp only [eq_self_iff_true, true_or],
    simp only [h_3] },
  { split_ifs, cases h_3,
    simp only [eq_self_iff_true, true_or, true_iff], exact ⟨cell, h_1.symm⟩,
    rw or_iff_right h_3 },
  { cases h_2, split_ifs, cases h_3, 
    simp only [eq_self_iff_true, and_true, true_or, iff_true], exact cell,
    rw or_iff_right h_3 },
  { rw and.congr_right_iff, intro hij,
    split_ifs, cases h_3, simp only [ne.symm h_1, ne.symm h_2], refl },
end

-- new strip of k's + (box if T h.i h.j = k) = 
-- (old strip of k's) + (box if h.val = k)

lemma ssyt.wt_replace {μ : young_diagram} (T : ssyt μ) (val : ℕ)
  (h : T.legal) (cell : (h.i, h.j) ∈ μ) :
  (h.replace cell).wt val + ite (val = T h.i h.j) 1 0 =
  T.wt val + ite (val = h.val) 1 0 :=
begin
  have key := T.strip_replace val h cell,
  rw [ssyt.wt, ssyt.wt],
  split_ifs; split_ifs at key,
  { rw [finset.insert_eq_of_mem, finset.insert_eq_of_mem] at key, rw key,
    rw ssyt.mem_strip, exact ⟨cell, h_1.symm⟩,
    rw [ssyt.mem_strip, h.entry_replace, if_pos rfl], exact ⟨cell, h_2.symm⟩ },
  { rw [add_zero, ← key, finset.card_insert_of_not_mem],
    rw [ssyt.mem_strip, ssyt.legal.entry_replace, if_pos rfl],
    exact λ h, ne.symm h_2 h.2 },
  { rw [key, add_zero, finset.card_insert_of_not_mem],
    rw ssyt.mem_strip,
    exact λ h, ne.symm h_1 h.2 },
  { rw [key, add_zero] },
end

end weight

-- example {μ : young_diagram} (T : ssyt μ) {i : ℕ} : string :=
--   string.intercalate ", " 
--     (list.map (λ j, (T i j).repr) (list.range (μ.row_len i))

section repr

def ssyt.repr {μ : young_diagram} (T : ssyt μ) : string :=
string.intercalate "\n" $
  ("shape: " ++ μ.repr) :: 
    list.map (λ i, string.intercalate ", " $
      list.map (λ j, (T i j).repr) (list.range $ μ.row_len i))
        (list.range $ μ.col_len 0)

instance ssyt.has_repr {μ : young_diagram} : has_repr (ssyt μ) :=
{ repr := ssyt.repr }

end repr

section examples

@[simp] def young_diagram.highest_ssyt (μ : young_diagram) : ssyt μ :=
{ entry := λ i j, ite ((i, j) ∈ μ) i 0,
  row_weak := λ i j1 j2 hj hcell, begin
    rw if_pos hcell, rw if_pos (μ.nw_of (le_refl _) (le_of_lt hj) hcell),
  end,
  col_strict := λ i1 i2 j hi hcell, begin
    rw if_pos hcell, rwa if_pos (μ.nw_of (le_of_lt hi) (le_refl _) hcell),
  end,
  zeros' := λ i j hij, by rw if_neg hij,
}

-- if μ.col_len j = i then μ.col_len 0, otherwise increasing with i
-- i + μ.col_len 0 - μ.col_len j
def young_diagram.lowest_ssyt (μ : young_diagram) : ssyt μ :=
{ entry := λ i j, ite ((i, j) ∈ μ) (i + μ.col_len 0 - μ.col_len j) 0,
  row_weak := λ i j1 j2 hj hcell, begin
    rw [if_pos hcell, if_pos (μ.nw_of (le_refl _) (le_of_lt hj) hcell)],
    apply nat.sub_le_sub_left,
    apply young_diagram.col_len_decr,
    exact le_of_lt hj,
  end,
  col_strict := λ i1 i2 j hi hcell, begin
    rw [if_pos hcell, if_pos (μ.nw_of (le_of_lt hi) (le_refl _) hcell)],
    apply nat.sub_mono_left_strict _ (add_lt_add_right hi _),
    exact (μ.col_len_decr (nat.zero_le j)).trans le_add_self,
  end,
  zeros' := λ i j not_cell, by rw if_neg not_cell
}

end examples