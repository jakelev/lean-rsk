import tactic
import recording_tableau

section biword

abbreviation rsk_le := (prod.lex.has_le ℕ ℕ).le

lemma rsk_mono_iff {x y : lex (ℕ × ℕ)} {w : list (lex (ℕ × ℕ))} : 
  (x :: y :: w).sorted (≤) ↔ 
  (x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2) ∧ (y :: w).sorted (≤) :=
begin
  repeat {rw list.sorted_cons at *},
  split; intro h,
  { exact ⟨(prod.lex_def _ _).mp (h.1 y (or.inl rfl)), h.2⟩ },
  { split, rotate, exact h.2,
    intros b hb,
    apply @le_trans _ _ _ y _ ((prod.lex_def _ _).mpr h.1),
    cases hb, exact le_of_eq hb.symm, exact h.2.1 b hb },
end

def wtR (w : list (lex (ℕ × ℕ))) (val : ℕ) : ℕ := 
list.count val $ w.map prod.fst

def wtB (w : list (lex (ℕ × ℕ))) (val : ℕ) : ℕ := 
list.count val $ w.map prod.snd

lemma wtR_cons (x : lex (ℕ × ℕ)) (w : list (lex (ℕ × ℕ))) (val : ℕ) :
  wtR (x :: w) val = ite (val = x.1) 1 0 + wtR w val :=
begin
  unfold wtR,
  rw [list.map_cons, list.count_cons, ite_add, zero_add, add_comm],
end

lemma wtB_cons (x : lex (ℕ × ℕ)) (w : list (lex (ℕ × ℕ))) (val : ℕ) :
  wtB (x :: w) val = ite (val = x.2) 1 0 + wtB w val :=
begin
  unfold wtB,
  rw [list.map_cons, list.count_cons, ite_add, zero_add, add_comm],
end

end biword

section rsk_inductive

def ssyt.rec_cert.rsk_inductive :
  Π {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B)
  (w : list (lex (ℕ × ℕ)))
  (hw : ((rcert.recval, rcert.bumpval) :: w).sorted rsk_le),
Σ {ν : young_diagram}, ssyt ν × ssyt ν
| μ R B rcert [] _ := 
  ⟨_, ⟨rcert.rsk_step.2.1, rcert.rsk_step.2.2⟩⟩
| μ R B rcert ((recval', bumpval') :: xs) hw := 
  ssyt.rec_cert.rsk_inductive
    (rcert.next_cert recval' bumpval' (rsk_mono_iff.mp hw).1)
    xs (rsk_mono_iff.mp hw).2

lemma ssyt.rec_cert.rsk_inductive_size :
  Π {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B)
  (w : list (lex (ℕ × ℕ)))
  (hw : ((rcert.recval, rcert.bumpval) :: w).sorted rsk_le),
  (rcert.rsk_inductive w hw).1.size =
  μ.size + 1 + w.length
| μ R B rcert [] _ := by apply B.row_bump_size
| μ R B rcert ((recval', bumpval') :: xs) hw := begin
  rw ssyt.rec_cert.rsk_inductive,
  rw [ssyt.rec_cert.rsk_inductive_size, add_assoc, add_comm 1],
  rw [B.row_bump_size rcert.bumpval, list.length_cons],
end

lemma ssyt.rec_cert.rsk_inductive_wtR :
  Π {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B)
  (w : list (lex (ℕ × ℕ)))
  (hw : ((rcert.recval, rcert.bumpval) :: w).sorted rsk_le)
  (val : ℕ),
  (rcert.rsk_inductive w hw).2.1.wt val =
  R.wt val + (ite (val = rcert.recval) 1 0) + wtR w val
| μ R B rcert [] _ val := begin
  unfold wtR, rw [list.map_nil, list.count_nil, add_zero],
  exact rcert.rec_wt val,
end
| μ R B rcert ((recval', bumpval') :: xs) hw val := begin
  rw [← rcert.rec_wt val, wtR_cons, ← add_assoc],
  rw ssyt.rec_cert.rsk_inductive,
  rw ssyt.rec_cert.rsk_inductive_wtR, refl,
end

lemma ssyt.rec_cert.rsk_inductive_wtB :
  Π {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B)
  (w : list (lex (ℕ × ℕ)))
  (hw : ((rcert.recval, rcert.bumpval) :: w).sorted rsk_le)
  (val : ℕ),
  (rcert.rsk_inductive w hw).2.2.wt val =
  B.wt val + (ite (val = rcert.bumpval) 1 0) + wtB w val
| μ R B rcert [] _ val := begin
  unfold wtB, rw [list.map_nil, list.count_nil, add_zero],
  exact B.row_bump_wt _ val,
end
| μ R B rcert ((recval', bumpval') :: xs) hw val := begin
  rw [← B.row_bump_wt _ val, wtB_cons, ← add_assoc],
  rw ssyt.rec_cert.rsk_inductive,
  rw ssyt.rec_cert.rsk_inductive_wtB, refl,
end

end rsk_inductive

section rsk

def rsk_start_cert (recval bumpval : ℕ) : ssyt.rec_cert T_empty T_empty :=
{ recval := recval, bumpval := bumpval,
  rec_le := λ _ _, nat.zero_le _,
  rec_eq_left := λ _ _ cell _, false.rec _ cell }

def rsk :
  Π (w : list (lex (ℕ × ℕ))) (hw : w.sorted rsk_le),
  Σ (μ : young_diagram), ssyt μ × ssyt μ
| [] _ := ⟨∅, ∅, ∅⟩
| [(recval, bumpval)] _ :=
  (rsk_start_cert recval bumpval).rsk_step
| ((recval, bumpval) :: rb' :: xs) hw :=
  (rsk_start_cert recval bumpval).rsk_inductive (rb' :: xs) hw

lemma rsk_size :
  Π (w : list (lex (ℕ × ℕ))) (hw : w.sorted rsk_le),
  (rsk w hw).1.size = w.length
| [] _ := rfl
| [(recval, bumpval)] _ := by apply young_diagram.outer_corner.add_size
| ((recval, bumpval) :: rb' :: xs) hw := by {
  rw [rsk, ssyt.rec_cert.rsk_inductive_size, 
      μ_empty_size, zero_add, add_comm], refl,
}

lemma rsk_wtR :
  Π (w : list (lex (ℕ × ℕ))) (hw : w.sorted rsk_le) (val : ℕ),
  (rsk w hw).2.1.wt val = wtR w val
| [] _ val := rfl
| [(recval, bumpval)] _ val := begin
  rw [rsk, ssyt.rec_cert.rsk_step, ssyt.rec_cert.rec_wt, T_empty_wt, zero_add],
  refl,
end
| ((recval, bumpval) :: rb' :: xs) hw val := by {
  rw [wtR_cons, rsk, ssyt.rec_cert.rsk_inductive_wtR, T_empty_wt, zero_add],
  refl,
}

lemma rsk_wtB :
  Π (w : list (lex (ℕ × ℕ))) (hw : w.sorted rsk_le) (val : ℕ),
  (rsk w hw).2.2.wt val = wtB w val
| [] _ val := rfl
| [(recval, bumpval)] _ val := begin
  rw [rsk, ssyt.rec_cert.rsk_step, ssyt.row_bump_wt, T_empty_wt, zero_add],
  refl,
end
| ((recval, bumpval) :: rb' :: xs) hw val := by {
  rw [wtB_cons, rsk, ssyt.rec_cert.rsk_inductive_wtB, T_empty_wt, zero_add],
  refl,
}

end rsk