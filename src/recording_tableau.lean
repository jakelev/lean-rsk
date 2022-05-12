import tactic
import row_bump

section recording_tableau

section rec_cert

structure ssyt.rec_cert {μ : young_diagram} (R B : ssyt μ) :=
  (recval bumpval : ℕ)
  (rec_le : ∀ i j, R i j ≤ recval)
  (rec_eq_left : ∀ i j (cell : (i, j) ∈ μ),
      R i j = recval → j < (B.row_bump bumpval).1.j)

def ssyt.rec_cert.to_legal
  {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B) : R.legal :=
{ i := (B.row_bump rcert.bumpval).1.i,
  j := (B.row_bump rcert.bumpval).1.j,
  val := rcert.recval,
  cell_left := (B.row_bump rcert.bumpval).1.cell_left,
  cell_up := (B.row_bump rcert.bumpval).1.cell_up,
  left := λ _ _, rcert.rec_le _ _,
  right := λ j hj cell, absurd (μ.nw_of (le_refl _) (le_of_lt hj) cell) 
                               (B.row_bump rcert.bumpval).1.not_cell,
  up := λ i hi, 
    lt_of_le_of_ne (rcert.rec_le _ _)
      (λ h, (lt_self_iff_false _).mp $
        rcert.rec_eq_left _ _ ((B.row_bump rcert.bumpval).1.cell_up hi) h),
  down := λ i hi cell, absurd (μ.nw_of (le_of_lt hi) (le_refl _) cell) 
                               (B.row_bump rcert.bumpval).1.not_cell
}

end rec_cert

section rec_step

def ssyt.rec_cert.rec_step
  {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B) :
  ssyt (B.row_bump rcert.bumpval).1.add :=
rcert.to_legal.add (B.row_bump rcert.bumpval).1.not_cell

lemma ssyt.rec_cert.rec_entry
  {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B) (i j : ℕ) :
  rcert.rec_step i j =
  ite ((i, j) = (rcert.to_legal.i, rcert.to_legal.j)) rcert.to_legal.val (R i j) := rfl

lemma ssyt.rec_cert.rec_wt
  {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B) (val : ℕ) :
  rcert.rec_step.wt val = R.wt val + ite (val = rcert.recval) 1 0 :=
by apply ssyt.wt_add

def ssyt.rec_cert_of_gt {μ : young_diagram} (R B : ssyt μ) (recval bumpval : ℕ)
  (h_lt : ∀ i j (cell : (i, j) ∈ μ), R i j < recval) : ssyt.rec_cert R B :=
{ bumpval := bumpval, recval := recval,
  rec_le := λ i j, dite ((i, j) ∈ μ) 
    (λ cell, le_of_lt $ h_lt _ _ cell)
    (λ not_cell, (R.zeros not_cell).symm ▸ nat.zero_le recval),
  rec_eq_left := λ _ _ cell h_eq, false.rec _ $ ne_of_lt (h_lt _ _ cell) h_eq }

def ssyt.rec_cert.next_cert
  {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B)
  (recval' bumpval' : ℕ) 
  (h : rcert.recval < recval' ∨ 
       (rcert.recval = recval' ∧ rcert.bumpval ≤ bumpval')) :
ssyt.rec_cert rcert.rec_step (B.row_bump rcert.bumpval).2 :=
{ bumpval := bumpval', recval := recval',
  rec_le := λ i j, begin
    apply @le_trans _ _ _ rcert.recval,
      rw ssyt.rec_cert.rec_entry,
      split_ifs, refl, apply rcert.rec_le,
    cases h, exact le_of_lt h, exact le_of_eq h.1,
  end,
  rec_eq_left := λ i j cell h_eq, begin
    cases h,
      { exfalso, apply ne_of_lt (lt_of_le_of_lt _ h) h_eq,
        rw rcert.rec_entry, split_ifs, refl, apply rcert.rec_le },
      { cases h.1,
        apply lt_of_le_of_lt _,
        apply ssyt.rbs_cert.rbwf_pieri _ _, refl, exact h.2,
        rw rcert.rec_entry at h_eq, split_ifs at h_eq,
          { cases h_1, refl },
          { apply le_of_lt (rcert.rec_eq_left i j _ h_eq),
            rw young_diagram.outer_corner.mem_add at cell,
            exact cell.resolve_left h_1 }
      }
  end
}

end rec_step

end recording_tableau