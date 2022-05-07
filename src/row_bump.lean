import tactic
import row_insertion

/-

Defining "row_bump" by successive row insertions

Given an ssyt T and natural numbers i, k, we insert k into T in row i, then
insert the bumped-out entry into row i+1, and so on, until the inserted
entry goes at the end of the row.

This is defined using well-founded recursion.

Analogs of each of the lemmas shown for ssyt.rbs and ssyt.rbs_end are shown here.

The key lemma is the *"pieri" property*: if we bump in k, then k' ≥ k starting from
the same row, the first final position is < the second final position. This is
essentially an immediate consequence of ssyt.rbs_cert.rbc_le_rbc and some commutativity
statements. This lemma is necessary to define the recording tableau.
-/

section row_bump_well_founded

def ssyt.rbs_cert.bound {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) : ℕ :=
μ.col_len 0 - h.i

lemma ssyt.rbs_cert.bound_decr {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (cell : (h.i, h.j) ∈ μ) : (h.next_cert cell).bound < h.bound :=
begin
  apply nat.sub_mono_right_strict _ _,
  rw [h.next_cert_i, nat.succ_le_iff, ← μ.mem_col_iff'],
  exact μ.nw_of (le_refl _) (nat.zero_le _) cell,
  exact lt_add_one h.i,
end

def ssyt.rbs_cert.rbwf {μ : young_diagram} : 
Π {T : ssyt μ} (h : T.rbs_cert), Σ (c : μ.outer_corner), ssyt c.add
| T h := dite ((h.i, h.j) ∈ μ)
  (λ cell, have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
           (h.next_cert cell).rbwf)
  (λ not_cell, ⟨_, h.rbs_end not_cell⟩)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

-- @[reducible] def ssyt.rbs_cert.rbwf_shape
--   {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) := h.rbwf.1.add
-- @[reducible] def ssyt.rbs_cert.rbwf_ssyt
--   {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) := h.rbwf.2

@[simp]
lemma ssyt.rbs_cert.rbwf_of_cell {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
 (cell : (h.i, h.j) ∈ μ) : h.rbwf = (h.next_cert cell).rbwf :=
by rw [ssyt.rbs_cert.rbwf, dif_pos cell]

@[simp]
lemma ssyt.rbs_cert.rbwf_of_not_cell {μ : young_diagram} {T : ssyt μ} 
  (h : T.rbs_cert) (not_cell : (h.i, h.j) ∉ μ) : 
  h.rbwf = ⟨_, h.rbs_end not_cell⟩ :=
by rw [ssyt.rbs_cert.rbwf, dif_neg not_cell]

lemma ssyt.rbs_cert.rbwf_size {μ : young_diagram} :
Π {T : ssyt μ} (h : T.rbs_cert), h.rbwf.1.add.size = μ.size + 1
| T h := dite ((h.i, h.j) ∈ μ)
  (λ cell, 
    have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
    by rw [h.rbwf_of_cell cell, ssyt.rbs_cert.rbwf_size])
  (λ not_cell, begin
    rw h.rbwf_of_not_cell not_cell,
    apply young_diagram.outer_corner.add_size,
  end)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

lemma ssyt.rbs_cert.rbwf_wt {μ : young_diagram} :
Π {T : ssyt μ} (h : T.rbs_cert) (val : ℕ),
h.rbwf.2.wt val = T.wt val + ite (val = h.val) 1 0
| T h := λ val, dite ((h.i, h.j) ∈ μ)
  (λ cell, 
    have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
    begin
      rw [h.rbwf_of_cell cell, ssyt.rbs_cert.rbwf_wt],
      apply ssyt.wt_replace,
    end)
  (λ not_cell, begin
    rw h.rbwf_of_not_cell not_cell,
    apply ssyt.wt_add,
  end)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

lemma ssyt.rbs_cert.rbwf_shape_eq_self_lt_initial_row {μ : young_diagram} :
Π {T : ssyt μ} (h : T.rbs_cert) (i j : ℕ) (hi : i < h.i), 
  (i, j) ∈ h.rbwf.1.add ↔ (i, j) ∈ μ
| T h := λ i j hi, dite ((h.i, h.j) ∈ μ)
  (λ cell, 
    have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
    begin
      rw [h.rbwf_of_cell cell, ssyt.rbs_cert.rbwf_shape_eq_self_lt_initial_row],
      exact hi.trans (lt_add_one _),
    end)
  (λ not_cell, begin
    rw [h.rbwf_of_not_cell not_cell, h.rbs_end_shape_eq_of_ne_row _ (ne_of_lt hi)],
  end)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

lemma ssyt.rbs_cert.rbwf_eq_self_lt_initial_row {μ : young_diagram} :
Π {T : ssyt μ} (h : T.rbs_cert) (i j : ℕ) (hi : i < h.i), h.rbwf.2 i j = T i j
| T h := λ i j hi, dite ((h.i, h.j) ∈ μ)
  (λ cell, 
    have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
    begin
      rw [h.rbwf_of_cell cell, ssyt.rbs_cert.rbwf_eq_self_lt_initial_row],
      apply h.rbs_entry_eq_of_ne_row _ (ne_of_lt hi),
      exact hi.trans (lt_add_one _),
    end)
  (λ not_cell, begin
    rw h.rbwf_of_not_cell not_cell,
    apply h.rbs_end_entry_eq_of_ne_row not_cell (ne_of_lt hi),
  end)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

end row_bump_well_founded

section pieri

lemma ssyt.rbs_cert.rbwf_j_le {μ : young_diagram} :
Π {T : ssyt μ} (h : T.rbs_cert), h.rbwf.1.j ≤ h.j
| T h := dite ((h.i, h.j) ∈ μ)
  (λ cell, 
    have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
    begin
      rw h.rbwf_of_cell cell,
      apply le_trans _ (h.next_rbc_le cell),
      apply ssyt.rbs_cert.rbwf_j_le,
    end)
  (λ not_cell, begin
    rw h.rbwf_of_not_cell not_cell, refl,
  end)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

-- lemma ssyt.rbs_cert.rbwf_j_le_rbc {μ : young_diagram} {T : ssyt μ} 
--   (h : T.rbs_cert) (h' : h.rbwf.2.rbs_cert)
--   (hi : h'.i < h.i) (hval : h.val ≤ h'.val) :
--   h.rbwf.1.j < h'.j :=
-- begin
--   apply lt_of_le_of_lt _ _, use h.j,
--   apply h.rbwf_j_le,
--   rw [ssyt.lt_rbc_iff],
--   split, sorry,
--   apply le_trans _ hval,
--   sorry,
--   -- apply h.rbc_lt_rbc,
-- end

/-

Setup:

  T
  ↓h
  T1  `→h'_1` T12
  ↓h1         `↓h1_2`
  :           `T12f →h12f ..`
  T1f    →h'   T1f2 →h'' ..  


-/


lemma ssyt.rbs_cert.rbwf_pieri {μ : young_diagram} :
Π {T : ssyt μ} (h : T.rbs_cert) (h' : h.rbwf.2.rbs_cert)
  (hi : h'.i = h.i) (hval : h.val ≤ h'.val),
  h.rbwf.1.j < h'.rbwf.1.j
| T h := dite ((h.i, h.j) ∈ μ)
  (λ cell, begin 
    rw h.rbwf_of_cell cell,
    set T1 := h.rbs cell,
    set h1 : T1.rbs_cert := h.next_cert cell,
    set T1f := h1.rbwf.2,
    intro h',
    by_cases cell' : (h'.i, h'.j) ∈ (h.next_cert cell).rbwf.1.add,
    { rw h'.rbwf_of_cell cell',
      intros hi hval,
      set T1f2 := h'.rbs cell',
      set h'' : T1f2.rbs_cert := h'.next_cert cell',

      -- copy certs to T1
      set h'_1 : T1.rbs_cert := h'.copy T1 
        (λ i' j' hi', by {
          rw ssyt.rbs_cert.rbwf_shape_eq_self_lt_initial_row,
          exact nat.lt_succ_iff.mpr (hi ▸ hi') })
        (λ i' j' hi', by {
          rw ssyt.rbs_cert.rbwf_eq_self_lt_initial_row,
          exact nat.lt_succ_iff.mpr (hi ▸ hi') }),
      have cell'_1 : (h'_1.i, h'_1.j) ∈ μ := by {
        rw ssyt.rbs_cert.copy_j,
        rw ssyt.rbs_cert.rbwf_shape_eq_self_lt_initial_row at cell',
        exact cell',
        rw hi, exact lt_add_one _,
      },

      set T12 := h'_1.rbs cell'_1,
      set h1_2 := h1.copy' T12 
        (λ _ _ _, id) 
        (λ _, iff.rfl)
        (λ i' j' hi', by apply ssyt.rbs_cert.rbs_entry_le) 
        (λ j', by { rw h'_1.rbs_entry_eq_of_ne_row,
                    change h.i.succ ≠ h'.i, rw hi, 
                    exact h.i.succ_ne_self }),
      set T12f := h1_2.rbwf.2,
      set h12f : T12f.rbs_cert := h''.copy' T12f sorry sorry sorry sorry,
      have key :=
        have wf : h1_2.bound < h.bound := h.bound_decr cell,
        ssyt.rbs_cert.rbwf_pieri h1_2 h12f,
      
      rw (_ : h1.rbwf.fst.j = h1_2.rbwf.fst.j),
      rw (_ : h''.rbwf.fst.j = h12f.rbwf.fst.j),
      apply key,
      change h'.i.succ = h.i.succ, rw hi,
      change h1.val ≤ h''.val,
      change h.out ≤ h'.out,
      { change T _ _ ≤ T1f _ _,
        rw hi,
        rw h1.rbwf_eq_self_lt_initial_row _ _ (lt_add_one _),
        have : h'.j = h'_1.j := by rw ssyt.rbs_cert.copy_j, rw this,
        convert h.rbc_out_le_rbc_out cell hval _,
        rw ← hi, refl,
        rw ← hi, exact cell'_1 },
      { 
        sorry },
      { 
        sorry },
    },
    { rename cell' not_cell',
      rw h'.rbwf_of_not_cell not_cell',
      intros hi hval, change _ < h'.j,
      apply lt_of_le_of_lt _ _, use h1.j,
      apply h1.rbwf_j_le,
      apply lt_of_le_of_lt (h.next_rbc_le cell),

      by_contra h_le, push_neg at h_le, apply not_cell',
      rw hi, apply young_diagram.nw_of _ (le_refl _) h_le,
      rw young_diagram.outer_corner.mem_add, right, exact cell },
  end)
  (λ not_cell, begin 
    rw h.rbwf_of_not_cell not_cell,
    intros h' hi hval,
    have key : h.j < h'.j,
    { rw [ssyt.lt_rbc_iff, hi], split,
      { rw young_diagram.outer_corner.mem_add,
        exact or.inl rfl },
      { rw [h.rbs_end_entry, if_pos rfl],
        exact hval, }, },
    rwa h'.rbwf_of_not_cell,
    rw [hi, young_diagram.outer_corner.mem_add], push_neg,
    exact ⟨λ h_eq, (ne_of_lt key).symm (prod.mk.inj_iff.mp h_eq).2,
           λ cell', not_cell (μ.nw_of (le_refl _) (le_of_lt key) cell')⟩,
  end)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

end pieri

-- section experimental

-- lemma ssyt.rbs_cert.not_cell_of_bound_zero {μ : young_diagram} {T : ssyt μ} 
--   (h : T.rbs_cert) (hzero : h.bound = 0) : (h.i, h.j) ∉ μ :=
-- begin
--   intro cell,
--   rw [ssyt.rbs_cert.bound, nat.sub_eq_zero_iff_le] at hzero,
--   apply not_lt_of_le hzero,
--   rw ← μ.mem_col_iff',
--   exact μ.nw_of (le_refl _) (nat.zero_le _) cell,
-- end

-- lemma ssyt.rbs_cert.next_bound_succ {μ : young_diagram} {T : ssyt μ} 
--   (h : T.rbs_cert) (cell : (h.i, h.j) ∈ μ) : 
--   (h.next_cert cell).bound.succ = h.bound :=
-- begin
--   rw [ssyt.rbs_cert.bound, ssyt.rbs_cert.bound, h.next_cert_i, 
--       nat.sub_succ, nat.succ_pred_eq_of_pos],
--   apply nat.sub_pos_of_lt,
--   rw ← μ.mem_col_iff',
--   exact μ.nw_of (le_refl _) (nat.zero_le _) cell,
-- end

-- -- bump in until no longer able (but don't do the last step)
-- def ssyt.rbs_cert.rbwf'' {μ : young_diagram} : Π {T : ssyt μ} (h : T.rbs_cert), ssyt μ
-- | T h := dite ((h.i, h.j) ∈ μ)
--           (λ cell, have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
--                    (h.next_cert cell).rbwf'')
--           (λ _, T)
-- using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

-- @[simp]
-- lemma ssyt.rbs_cert.rbwf''_of_cell {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
--  (cell : (h.i, h.j) ∈ μ) : (h.next_cert cell).rbwf'' = h.rbwf'' :=
-- begin 
--   symmetry, rw [ssyt.rbs_cert.rbwf'', dif_pos cell],
-- end

-- -- def ssyt.rbs_cert.rbwf_last_cert {μ : young_diagram} : 
-- --   Π {T : ssyt μ} (h : T.rbs_cert), h.rbwf.rbs_cert
-- -- | T h := dite ((h.i, h.j) ∈ μ)
-- --           (λ cell, have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
-- --                    begin
-- --                      set key1 := (h.next_cert cell).rbwf_last_cert,
-- --                      have key2 := (h.rbwf_of_cell cell),
-- --                      rwa key2 at key1,
-- --                    end)
-- --           (λ _, begin 

-- --           end)
-- -- using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }


-- def ssyt.rbs_cert.rbwf_pre {μ : young_diagram} : Π {T : ssyt μ} (h : T.rbs_cert), 
--   Σ' (T' : ssyt μ) (h' : T'.rbs_cert), (h'.i, h'.j) ∉ μ
-- | T h := dite ((h.i, h.j) ∈ μ)
--           (λ cell, have wf : (h.next_cert cell).bound < h.bound := h.bound_decr cell,
--                    (h.next_cert cell).rbwf_pre)
--           (λ not_cell, ⟨T, h, not_cell⟩)
-- using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.bound)⟩] }

-- def ssyt.rbs_cert.rbwf' {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
--   : Σ ν, ssyt ν := ⟨_, h.rbwf_pre.2.1.rbs_end h.rbwf_pre.2.2⟩
--   -- := h.rbwf_pre.2.1.rbs_end h.rbwf_pre.2.2

-- def ssyt.rb_ind : Π (b : ℕ) 
--   {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) (hb : h.bound = b),
--   Σ ν, ssyt ν
-- | 0 := λ μ T h hb, ⟨_, h.rbs_end (h.not_cell_of_bound_zero hb)⟩
-- | (nat.succ b) := λ μ T h hb, 
--   dite ((h.i, h.j) ∈ μ)
--   (λ cell, ssyt.rb_ind b (h.next_cert cell) 
--     (nat.succ.inj $ (h.next_bound_succ cell).trans hb))
--   (λ not_cell, ⟨_, h.rbs_end not_cell⟩)



-- #check ssyt.rbs_cert.rbwf'

-- end experimental

-- #eval μ5331.lowest_ssyt
-- #eval (μ5331.lowest_ssyt.rbs_start_cert 0).rbwf
-- #eval (μ5331.lowest_ssyt.rbs_start_cert 1).rbwf
-- #eval (μ5331.lowest_ssyt.rbs_start_cert 3).rbwf
-- #eval ssyt.rb_ind 4 (μ5331.lowest_ssyt.rbs_start_cert 0) sorry