import tactic
import recording_tableau

section rsk_inductive

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

def ssyt.rec_cert.rsk_inductive :
  Π {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B)
  (w : list (lex (ℕ × ℕ)))
  (hw : ((rcert.recval, rcert.bumpval) :: w).sorted rsk_le),
Σ {ν : young_diagram}, ssyt ν × ssyt ν
| μ R B rcert [] _ := ⟨_, ⟨rcert.rsk_step.2.1, rcert.rsk_step.2.2⟩⟩
| μ R B rcert ((recval', bumpval') :: xs) hw := 
  dite (rcert.recval < recval')
  (λ h_lt, ssyt.rec_cert.rsk_inductive
             (rcert.next_cert_of_gt recval' bumpval' h_lt)
             xs (rsk_mono_iff.mp hw).2)
  (λ h_not_lt, ssyt.rec_cert.rsk_inductive
      (rcert.next_cert bumpval' 
        ((rsk_mono_iff.mp hw).1.resolve_left h_not_lt).2)
      xs (by { convert (rsk_mono_iff.mp hw).2,
               exact ((rsk_mono_iff.mp hw).1.resolve_left h_not_lt).1}))

def wtR' (w : list (lex (ℕ × ℕ))) (val : ℕ) : ℕ := 
list.count val $ w.map prod.fst

lemma wtR'_cons (x : lex (ℕ × ℕ)) (w : list (lex (ℕ × ℕ))) (val : ℕ) :
  wtR' (x :: w) val = ite (val = x.1) 1 0 + wtR' w val :=
begin
  unfold wtR',
  rw [list.map_cons, list.count_cons, ite_add, zero_add, add_comm],
end

def wtB' (w : list (lex (ℕ × ℕ))) (val : ℕ) : ℕ := 
list.count val $ w.map prod.snd

lemma ssyt.rec_cert.rsk_inductive_wt :
  Π {μ : young_diagram} {R B : ssyt μ} (rcert : ssyt.rec_cert R B)
  (w : list (lex (ℕ × ℕ)))
  (hw : ((rcert.recval, rcert.bumpval) :: w).sorted rsk_le)
  (val : ℕ),
  (rcert.rsk_inductive w hw).2.1.wt val =
  R.wt val + (ite (val = rcert.recval) 1 0) + wtR' w val
| μ R B rcert [] _ val := begin
  unfold wtR', rw [list.map_nil, list.count_nil, add_zero],
  exact rcert.rec_wt val,
end
| μ R B rcert ((recval', bumpval') :: xs) hw val := begin
  rw [← rcert.rec_wt val, wtR'_cons, ← add_assoc],
  rw ssyt.rec_cert.rsk_inductive, split_ifs,
    rw [dif_pos h, ssyt.rec_cert.rsk_inductive_wt], refl,
    rw [dif_neg h, ssyt.rec_cert.rsk_inductive_wt],
    convert rfl,
    exact ((rsk_mono_iff.mp hw).1.resolve_left h).1.symm,
end

    -- let tail_le := (rsk_mono_iff.mp hw).2 in
    -- let eq_and_le : rcert.recval = recval' ∧ rcert.bumpval ≤ bumpval' :=
    --   (rsk_mono_iff.mp hw).1.resolve_left h_not_lt in
    -- (rcert.next_cert bumpval' (by exact eq_and_le.2)).rsk_inductive 
    --   xs (by { change list.sorted rsk_le ((rcert.recval, bumpval') :: xs),
    --            exact eq_and_le.1.symm ▸ tail_le }))
  -- begin
  --   obtain ⟨h1, h2⟩ := rsk_mono_iff.mp hw,
  --   obtain ⟨h1a : rcert.recval = recval', h1b⟩ := h1.resolve_left h_not_lt,
  --   exact (rcert.next_cert bumpval' h1b).rsk_inductive xs (h1a.symm ▸ h2),
  -- end)



end rsk_inductive