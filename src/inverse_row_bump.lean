import tactic
import inverse_row_insertion

/-

Defining "inverse_row_bump" by successive inverse row insertions

This isn't figured out nicely yet. This file needs to define inverse row bumping
by repeated inverse_row_insertion. There are two challenges here:

1. Row bumping starts in an arbitrary row, so inverse row bumping should
  *end* in an arbitrary (given) row. This is a little awkward.
2. Inverse row bumping needs to have the reverse inductive structure to 
  forward row bumping. Forward row bumping is defined inductively as
    rbwf(T) = rbwf(rbs(T)) where rbs is one step
  so, inverse row bumping needs to be defined as
    irbwf(T) = irbs(irbwf(T)) where irbs is one step
  in other words, "do the first n-1 steps, then 1 more step" is the inverse
  of "do 1 step, then the last n-1 steps".

Currently I run into problems trying to prove that rbwf and irbwf are inverses
and also in trying to prove the analog of [row_bump.lean/ssyt.rbs_cert.rbwf_pieri]
since the statements are just kind of complicated...

I run into "motive not correct" errors involving dependent types. 
Also I'm not sure I have strong enough inductive statements.

Should the rbs_cert and irbs_cert structures be changed to not be structures?

-/

section inverse_row_bump

section irb_inductive

-- def ssyt.irbs_cert.irb_inductive :
--   Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
--   (end_after : ℕ) (i : ℕ) (hi : h.i = end_after + i), ssyt μ
-- | μ T h end_after 0 hi := h.irbs
-- | μ T h end_after (nat.succ n) hi :=
--   ssyt.irbs_cert.irb_inductive
--     (h.next_cert (by convert nat.succ_ne_zero _))
--     end_after n (by convert congr_arg nat.pred hi)
  -- why did these converts work??
  -- fuller definition:
  -- ssyt.irbs_cert.irb_inductive
  --   (h.next_cert (by { rw [hi, nat.add_succ], apply nat.succ_ne_zero }))
  --   end_after n (by { change h.i.pred = _, rw [hi, nat.add_succ, nat.pred_succ] })

-- stops before doing row i and stores the final irbs_cert
def ssyt.irbs_cert.irb_inductive :
  Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i),
  Σ (T : ssyt μ), T.irbs_cert
| μ T h end_before 0 hi := ⟨T, h⟩
| μ T h end_before (nat.succ n) hi :=
  ssyt.irbs_cert.irb_inductive
    (h.next_cert (by convert nat.succ_ne_zero _))
    (by convert congr_arg nat.pred hi)
-- why did these converts work??

lemma ssyt.irbs_cert.irb_inductive_def_zero
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before : ℕ} (hi : h.i = end_before + 0) :
  h.irb_inductive hi = ⟨T, h⟩ := rfl
lemma ssyt.irbs_cert.irb_inductive_def_pos
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before n : ℕ} (hi : h.i = end_before + n.succ) :
  h.irb_inductive hi =
  ssyt.irbs_cert.irb_inductive
    (h.next_cert (by convert nat.succ_ne_zero _))
    (by convert congr_arg nat.pred hi) := rfl


lemma ssyt.irbs_cert.irb_inductive_out_cert_row :
  Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i),
  (h.irb_inductive hi).2.i = end_before
| μ T h end_before 0 hi := hi
| μ T h end_before (nat.succ n) hi :=
begin
  rw ssyt.irbs_cert.irb_inductive,
  rw ssyt.irbs_cert.irb_inductive_out_cert_row,
end


-- can the induction be turned inside out here?
-- currently it is irb_inductive(T,n) = irb_inductive(T.next, n-1),
-- that is, do 1 step, then do by induction.
-- can it be changed to irb_inductive = irb_inductive(T, n-1).next ?
-- probably easier to show inverse!

lemma ssyt.irbs_cert.irb_inductive_wt :
  Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  (end_before : ℕ) (i : ℕ) (hi : h.i = end_before + i) (val : ℕ),
  (h.irb_inductive hi).1.wt val + ite (val = (h.irb_inductive hi).2.val) 1 0 =
  T.wt val + ite (val = h.val) 1 0
| μ T h end_before 0 hi val := rfl
| μ T h end_before (nat.succ n) hi val := begin
  rw [ssyt.irbs_cert.irb_inductive, ssyt.irbs_cert.irb_inductive_wt],
  apply ssyt.irbs_cert.irbs_wt,
end

lemma ssyt.irbs_cert.irb_inductive_entry_eq_self_of_gt_row :
Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  (i' j' : ℕ) (hi' : i' > h.i),
  (h.irb_inductive hi).1 i' j' = T i' j'
| μ T h end_before 0 hi i' j' hi' := rfl
| μ T h end_before (nat.succ n) hi i' j' hi' := begin
  rw [ssyt.irbs_cert.irb_inductive,
      ssyt.irbs_cert.irb_inductive_entry_eq_self_of_gt_row,
      h.irbs_entry_eq_of_ne_row (ne_of_gt hi')],
  exact lt_of_le_of_lt (nat.pred_le _) hi'
end

lemma ssyt.irbs_cert.irb_inductive_entry_eq_self_of_le_end :
Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  (i' j' : ℕ) (hi' : i' ≤ end_before),
  (h.irb_inductive hi).1 i' j' = T i' j'
| μ T h end_before 0 hi i' j' hi' := rfl
| μ T h end_before (nat.succ n) hi i' j' hi' := begin
  rw [ssyt.irbs_cert.irb_inductive,
      ssyt.irbs_cert.irb_inductive_entry_eq_self_of_le_end _ _ _ _ hi',
      h.irbs_entry_eq_of_ne_row],
  apply ne_of_lt (lt_of_le_of_lt hi' _),
  rw [hi, lt_add_iff_pos_right],
  apply nat.succ_pos,
end

lemma ssyt.irbs_cert.irb_inductive_entry_eq_self
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  (i' j' : ℕ) (hi' : i' ≤ end_before ∨ h.i < i') :
  (h.irb_inductive hi).1 i' j' = T i' j' :=
begin
  cases hi',
    rw ssyt.irbs_cert.irb_inductive_entry_eq_self_of_le_end, exact hi',
    rw ssyt.irbs_cert.irb_inductive_entry_eq_self_of_gt_row, exact hi',
end

-- could maybe be golfed
lemma ssyt.irbs_cert.irb_inductive_entry_eq_of_eq_mid :
Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  {ν : young_diagram} {T' : ssyt ν} (h' : T'.irbs_cert)
  (hi' : h'.i = h.i) (hval : h'.val = h.val)
  (eq_cell : ∀ i j (hi'' : end_before < i ∧ i ≤ h.i), (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_row_mid : ∀ i j (hi'' : end_before < i ∧ i ≤ h.i), T i j = T' i j)
  (i j : ℕ) (hi'' : end_before < i ∧ i ≤ h.i),
(h.irb_inductive hi).1 i j = 
(h'.irb_inductive (by {rw hi at hi', exact hi'})).1 i j
| μ T h end_before 0 hi
  ν T' h' 
  hi' hval eq_cell eq_row_mid
  i j hi'' := eq_row_mid _ _ ⟨hi''.1, hi''.2⟩
| μ T h end_before (nat.succ n) hi
  ν T' h' 
  hi' hval eq_cell eq_row_mid
  i j hi'' := 
begin
  have hi''' : end_before < h.i := 
    by { rw [hi, lt_add_iff_pos_right], apply nat.succ_pos },
  have hj : h'.j = h.j := by {
    rw [ssyt.irbs_cert.j, ssyt.irbs_cert.j],
    apply T'.irbc_eq_of_eq_row' T,
      intro j, rw [hi', eq_cell _ _ ⟨hi''', by refl⟩],
      intro j, rw [hi', eq_row_mid _ _ ⟨hi''', by refl⟩],
      exact hi'.symm, exact hval.symm,
  },
  rw [ssyt.irbs_cert.irb_inductive, ssyt.irbs_cert.irb_inductive],
  cases lt_or_eq_of_le hi''.2,
  { apply ssyt.irbs_cert.irb_inductive_entry_eq_of_eq_mid,
      { exact congr_arg nat.pred hi' },
      { change T' _ _ = T _ _, rw [hi', hj, eq_row_mid _ _ ⟨hi''', by refl⟩] },
      { intros i' j' hij', 
        rw eq_cell _ _ ⟨hij'.1, hij'.2.trans (nat.pred_le _)⟩ },
      { intros i' j' hij',
        have key : i' < h.i,
          apply lt_of_le_of_lt hij'.2,
          apply nat.pred_lt (ne_of_gt _),
          apply lt_of_le_of_lt (nat.zero_le _) hi''',
        rw [h.irbs_entry_eq_of_ne_row (ne_of_lt key), 
            h'.irbs_entry_eq_of_ne_row (ne_of_lt _)],
        apply eq_row_mid _ _ ⟨hij'.1, le_of_lt key⟩,
        rw hi', exact key },
      { exact ⟨hi''.1, nat.le_pred_of_lt h_1⟩ }
   },
  { repeat {rw [ssyt.irbs_cert.irb_inductive_entry_eq_self_of_gt_row,
                ssyt.irbs_cert.irbs_entry]},
    rw [hi', hval, hj, eq_row_mid _ _ hi''],
    all_goals { change nat.pred _ < i, rw h_1 }, rw hi',
    all_goals { apply nat.pred_lt (ne_of_gt _),
                apply lt_of_le_of_lt (nat.zero_le _) hi''' }
  },
end

-- outputs the final tableau together with the removed value
def ssyt.irbs_cert.irb
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : ssyt μ × ℕ :=
  let out := h.irb_inductive (add_comm h.i 0) in
  (out.2.irbs, out.2.out)

lemma ssyt.irbs_cert.irb_wt
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) (val : ℕ) :
  h.irb.1.wt val + ite (val = h.irb.2) 1 0 =
  T.wt val + ite (val = h.val) 1 0 :=
begin
  rw ssyt.irbs_cert.irb,
  rw ssyt.irbs_cert.irbs_wt,
  apply ssyt.irbs_cert.irb_inductive_wt,
end

-- the full operation, starting from a corner
def ssyt.inverse_row_bump
  {μ : young_diagram} (T : ssyt μ) (c : μ.inner_corner) : ssyt c.del × ℕ :=
dite (c.i = 0) 
  (λ _, (T.del c, T c.i c.j))
  (λ pos, (T.irbs_cert_of_inner_corner c pos).irb)

-- three goals:
-- analog of [row_bump.lean/ssyt.rbs_cert.rbwf_pieri] to define inverse_rsk
-- irb_inductive' ∘ rbwf = id (start and end in row i)
-- rbwf ∘ irb_inductive' = id (start from an actual corner, not arbitrary)

end irb_inductive

section pieri

lemma ssyt.irbs_cert.irb_irbs_comm
  {μ : young_diagram} (T : ssyt μ) (h h1 : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  (h_h1_i : h1.i ≤ end_before ∨ h1.i > h.i)
  (h' : h1.irbs.irbs_cert) (hi' : h'.i = h.i) (hval' : h'.val = h.val)
  (h1' : (h.irb_inductive hi).1.irbs_cert) 
    (h1i' : h1'.i = h1.i) (h1val' : h1'.val = h1.val) :
∀ i' j', (h'.irb_inductive (by {rw hi at hi', use hi' })).1 i' j' =
          h1'.irbs i' j' :=
begin
  have hj : h1'.j = h1.j :=
    by { symmetry,
         apply ssyt.irbc_eq_of_eq_row' _ _ (λ _, iff.rfl) _ _ _ h1i' h1val',
         intro j, rw h.irb_inductive_entry_eq_self _ _ _ h_h1_i },
  intros i' j',
  by_cases h_i' : (i' ≤ end_before ∨ h'.i < i'),
  { rw [h'.irb_inductive_entry_eq_self _ _ _ h_i',
        h1'.irbs_entry, h1i', h1val', hj,
        h.irb_inductive_entry_eq_self _ _ _ _], 
    refl, exact hi' ▸ h_i' },
  { push_neg at h_i',
    rw h1'.irbs_entry_eq_of_ne_row,
    rw h.irb_inductive_entry_eq_of_eq_mid _ _ hi' hval'
      (λ _ _ _, iff.rfl) _ _, 
      rwa hi' at h_i',
      intros i'' j'' hi'', rw h1.irbs_entry_eq_of_ne_row,
      rintro rfl, apply absurd h_h1_i, push_neg, exact hi'',
    rintro rfl, rw [hi', h1i'] at h_i',
    apply absurd h_h1_i, push_neg, exact h_i' },
end




-- lemma ssyt.irbs_cert.irb_pieri :
-- Π {μ : young_diagram} (T : ssyt μ) (h : T.irbs_cert)
--   {end_before i : ℕ} (hi : h.i = end_before + i)
--   (h' : (h.irb_inductive hi).1.irbs_cert)
--   (hi' : h'.i = h.i) (hval' : h'.val ≤ h.val) (hj' : h'.j < h.j),
-- (h'.irb_inductive (by {rw hi at hi', use hi'})).2.j <
-- (h.irb_inductive hi).2.j
-- | μ T h end_before 0 hi := begin
--     rw ssyt.irbs_cert.irb_inductive, dsimp only,
--     intros h' hi' hval' hj',
--     apply absurd hj', push_neg,
--     rw ssyt.le_irbc_iff, rw hi', split, exact h.cell,
    
--     dsimp,
    
--     -- rw ssyt.irbc_lt_iff at hj',

--     rw ssyt.irbs_cert.irb_inductive, dsimp only at *,
--     rw [ssyt.irbc_lt_iff],
    
--     intro cell',
--     apply hval'.trans, --apply le_trans _ (T.row_weak hj' cell'),
--     have := h.out_lt_val,
    
    
--     -- rw ssyt.irbc_le_iff,

--     -- simp_rw ssyt.irbs_cert.irb_inductive,
-- end




end pieri

end inverse_row_bump

section inverse_row_bump'

-- stops before doing row i and stores the final irbs_cert
def ssyt.irbs_cert.irb_inductive' :
  Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i),
  Σ' (T : ssyt μ) (h : T.irbs_cert), h.i = end_before
| μ T h end_before 0 hi := ⟨T, h, hi⟩
| μ T h end_before (nat.succ n) hi :=
have hii : h.i = end_before.succ + n :=
  (hi.trans (end_before.succ_add_eq_succ_add n).symm),
⟨_,
 (h.irb_inductive' hii).2.1.next_cert (by { rw (h.irb_inductive' hii).2.2, apply nat.succ_ne_zero }),
 by {
   convert end_before.pred_succ,
   rw [ssyt.irbs_cert.next_cert_i, (h.irb_inductive' hii).2.2],
 }⟩

lemma ssyt.irbs_cert.irb_inductive'_row_zero
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before : ℕ} (hi : h.i = end_before + 0) :
  h.irb_inductive' hi = ⟨T, h, hi⟩ := rfl

lemma ssyt.irbs_cert.irb_inductive'_row_succ
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before n : ℕ} (hi : h.i = end_before + n.succ) :
  h.irb_inductive' hi =  
let out' := (h.irb_inductive'
    (hi.trans (end_before.succ_add_eq_succ_add n).symm)) in
  ⟨_, 
   out'.2.1.next_cert (by { rw out'.2.2, apply nat.succ_ne_zero }),
   by {
     change nat.pred _ = _, rw out'.2.2, apply nat.pred_succ,
   }⟩ := rfl

lemma ssyt.irbs_cert.irb_inductive'_out_row
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i) :
  (h.irb_inductive' hi).2.1.i = end_before := (h.irb_inductive' hi).2.2

-- lemma ssyt.irbs_cert.irb_inductive'_cert_val_zero
--   {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
--   {end_before : ℕ} (hi : h.i = end_before + 0) :
--   (h.irb_inductive' hi).2.1.val = h.val := rfl

-- lemma ssyt.irbs_cert.irb_inductive'_cert_val_succ
--   {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
--   {end_before n : ℕ} (hi : h.i = end_before + n.succ) :
--   (h.irb_inductive' hi).2.1.val =  
-- let out' := (h.irb_inductive'
--     (hi.trans (end_before.succ_add_eq_succ_add n).symm)) in
--   ⟨_, 
--    out'.2.1.next_cert (by { rw out'.2.2, apply nat.succ_ne_zero }),
--    by {
--      change nat.pred _ = _, rw out'.2.2, apply nat.pred_succ,
--    }⟩ := rfl

lemma ssyt.irbs_cert.irb_inductive'_wt :
  Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  (end_before : ℕ) (i : ℕ) (hi : h.i = end_before + i) (val : ℕ),
  (h.irb_inductive' hi).1.wt val + ite (val = (h.irb_inductive' hi).2.1.val) 1 0 =
  T.wt val + ite (val = h.val) 1 0
| μ T h end_before 0 hi val := rfl
| μ T h end_before (nat.succ n) hi val := begin
  rw ssyt.irbs_cert.irb_inductive'_row_succ, dsimp,
  simp_rw ssyt.irbs_cert.irbs_wt,
  rw ssyt.irbs_cert.irb_inductive'_wt,
end

lemma ssyt.irbs_cert.irb_inductive'_entry_eq_self_of_gt_row :
Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  (i' j' : ℕ) (hi' : i' > h.i),
  (h.irb_inductive' hi).1 i' j' = T i' j'
| μ T h end_before 0 hi i' j' hi' := rfl
| μ T h end_before (nat.succ n) hi i' j' hi' := begin
  rw ssyt.irbs_cert.irb_inductive'_row_succ, dsimp,
  rw [ssyt.irbs_cert.irbs_entry_eq_of_ne_row,
      ssyt.irbs_cert.irb_inductive'_entry_eq_self_of_gt_row _ _ _ _ hi'],
  rw ssyt.irbs_cert.irb_inductive'_out_row,
  apply ne_of_gt (lt_of_le_of_lt _ hi'),
  rw [hi, ← nat.succ_add_eq_succ_add], exact le_self_add,
end

lemma ssyt.irbs_cert.irb_inductive'_entry_eq_self_of_le_end :
Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  (i' j' : ℕ) (hi' : i' ≤ end_before),
  (h.irb_inductive' hi).1 i' j' = T i' j'
| μ T h end_before 0 hi i' j' hi' := rfl
| μ T h end_before (nat.succ n) hi i' j' hi' := begin
  rw ssyt.irbs_cert.irb_inductive'_row_succ, dsimp,
  rw [ssyt.irbs_cert.irbs_entry_eq_of_ne_row,
      ssyt.irbs_cert.irb_inductive'_entry_eq_self_of_le_end],
  exact nat.le_succ_of_le hi',
  apply ne_of_lt (lt_of_le_of_lt hi' _),
  rw ssyt.irbs_cert.irb_inductive'_out_row,
  exact lt_add_one _,
end

lemma ssyt.irbs_cert.irb_inductive'_entry_eq_self
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  (i' j' : ℕ) (hi' : i' ≤ end_before ∨ h.i < i') :
  (h.irb_inductive' hi).1 i' j' = T i' j' :=
begin
  cases hi',
    rw ssyt.irbs_cert.irb_inductive'_entry_eq_self_of_le_end, exact hi',
    rw ssyt.irbs_cert.irb_inductive'_entry_eq_self_of_gt_row, exact hi',
end

lemma ssyt.irbs_cert.irb_inductive'_eq_mid_of_eq_mid :
Π {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert)
  {end_before i : ℕ} (hi : h.i = end_before + i)
  {ν : young_diagram} {T' : ssyt ν} (h' : T'.irbs_cert)
  (hi' : h'.i = h.i) (hval : h'.val = h.val) (hj : h'.j = h.j)
  (eq_cell : ∀ i j (hi'' : end_before < i ∧ i ≤ h.i), (i, j) ∈ μ ↔ (i, j) ∈ ν)
  (eq_row_mid : ∀ i j (hi'' : end_before < i ∧ i ≤ h.i), T i j = T' i j),
(h.irb_inductive' hi).2.1.val = (h'.irb_inductive' (hi'.trans hi)).2.1.val
--∧ (h.irb_inductive' hi).2.1.j = (h'.irb_inductive' (hi'.trans hi)).2.1.j
∧ ∀ (i j : ℕ) (hi'' : end_before < i ∧ i ≤ h.i),
(h.irb_inductive' hi).1 i j = (h'.irb_inductive' (hi'.trans hi)).1 i j 
| μ T h end_before 0 hi
  ν T' h' 
  hi' hval hj eq_cell eq_row_mid := begin
    rw [h.irb_inductive'_row_zero, h'.irb_inductive'_row_zero], dsimp,
    exact ⟨hval.symm,
          --  hj.symm,
           eq_row_mid⟩,
  end
| μ T h end_before (nat.succ n) hi
  ν T' h' 
  hi' hval hj eq_cell eq_row_mid := 
begin
  have hi_succ : h.i = end_before.succ + n :=
    hi.trans (nat.succ_add_eq_succ_add _ _).symm,
  have hi'_succ : h'.i = end_before.succ + n :=
    hi'.trans hi_succ,
  -- have hi''' : end_before < h.i := 
  --   by { rw [hi, lt_add_iff_pos_right], apply nat.succ_pos },
  have hval'' : (h.irb_inductive' hi_succ).2.1.val = 
    (h'.irb_inductive' hi'_succ).2.1.val := by {
    rw (ssyt.irbs_cert.irb_inductive'_eq_mid_of_eq_mid
          _ _ _ hi' hval hj _ _).1,
    { rintros i' j' ⟨h1, h2⟩, rw eq_cell _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
    { rintros i' j' ⟨h1, h2⟩, rw eq_row_mid _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
  },
  have hj' : (h.irb_inductive' hi_succ).2.1.j = 
    (h'.irb_inductive' hi'_succ).2.1.j := by {
    sorry,
    -- cases n, exact hj.symm,
    -- -- rw ssyt.irbs_cert.irb_inductive'_row_succ,
    -- -- rw ssyt.irbs_cert.irb_inductive'_row_succ, dsimp,
    -- rw ssyt.irbs_cert.j, rw ssyt.irbs_cert.j,
    -- rw ssyt.irbc_eq_of_eq_row',
    -- -- { intro j, rw eq_cell _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
    -- intro j, rw eq_cell, rw [h.irb_inductive'_out_row, hi_succ], 
    -- exact ⟨lt_add_one _, nat.le_add_right _ _⟩,
    -- rotate, rw [h.irb_inductive'_out_row, h'.irb_inductive'_out_row],
    -- rw hval'',
    -- intro j, rw [h.irb_inductive'_out_row],
    -- rw ssyt.irbs_cert.irb_inductive'_row_succ,
    -- rw ssyt.irbs_cert.irb_inductive'_row_succ, dsimp,

    -- rw (ssyt.irbs_cert.irb_inductive'_eq_mid_of_eq_mid
    --       _ _ _ _ _ _ _ _).2,
    -- { rintros i' j' ⟨h1, h2⟩, rw eq_cell _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
    -- { rintros i' j' ⟨h1, h2⟩, rw eq_row_mid _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
  },

  rw [ssyt.irbs_cert.irb_inductive'_row_succ,
      ssyt.irbs_cert.irb_inductive'_row_succ], dsimp only,
  split,
  { dsimp, rw [ssyt.irbs_cert.out, ssyt.irbs_cert.out],
    rw [h.irb_inductive'_out_row, h'.irb_inductive'_out_row],
    rw ← hj',
    rw [h.irb_inductive'_entry_eq_self_of_le_end,
        h'.irb_inductive'_entry_eq_self_of_le_end, eq_row_mid],
    rw hi_succ, exact ⟨lt_add_one _, nat.le_add_right _ _⟩, refl, refl },
  -- split,
  -- { sorry ,
  --   -- rw ssyt.irbs_cert.j, rw ssyt.irbs_cert.j,
  --   -- rw ssyt.irbc_eq_of_eq_row',
  --   -- rotate 2,
  --   -- repeat {rw ssyt.irbs_cert.next_cert_i},
  --   -- rw [h.irb_inductive'_out_row, h'.irb_inductive'_out_row],
  --   -- sorry,
  --   -- intro j, rw [h.irb_inductive'_out_row, nat.pred_succ],
  -- },
  intros i j hi'',
  cases lt_or_eq_of_le (nat.succ_le_iff.mpr hi''.1),
  { rw [ssyt.irbs_cert.irbs_entry_eq_of_ne_row,
        ssyt.irbs_cert.irbs_entry_eq_of_ne_row,
        (ssyt.irbs_cert.irb_inductive'_eq_mid_of_eq_mid
          _ _ _ hi' hval hj _ _).2],
    exact ⟨h_1, hi''.2⟩,
    { rintros i' j' ⟨h1, h2⟩, rw eq_cell _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
    { rintros i' j' ⟨h1, h2⟩, rw eq_row_mid _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
    rw ssyt.irbs_cert.irb_inductive'_out_row, exact ne_of_gt h_1,
    rw ssyt.irbs_cert.irb_inductive'_out_row, exact ne_of_gt h_1 },
  
  subst i,
  rw [ssyt.irbs_cert.irbs_entry, ssyt.irbs_cert.irbs_entry],
  rw [h.irb_inductive'_out_row, h'.irb_inductive'_out_row, ← hj'],
  repeat {simp_rw [prod.mk.inj_iff, and_iff_right]},
  split_ifs,
  rw hval'',
  rw [h.irb_inductive'_entry_eq_self_of_le_end,
      h'.irb_inductive'_entry_eq_self_of_le_end,
      eq_row_mid _ _ hi''],
  refl, refl,
  

  -- rw [ssyt.irbs_cert.irbs_entry],
  -- -- rw [ssyt.irbs_cert.irbs_entry, ssyt.irbs_cert.irbs_entry],
  -- rw [ssyt.irbs_cert.irb_inductive'_out_row],
  -- rw if_neg,

  
  

  -- rw ssyt.irbs_cert.irb_inductive'_entry_eq_of_eq_mid,
  -- { rintros i' j' ⟨h1, h2⟩, rw eq_cell _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
  -- { rintros i' j' ⟨h1, h2⟩, rw eq_row_mid _ _ ⟨(lt_add_one _).trans h1, h2⟩ },
  -- exact ⟨h_1, hi''.2⟩,
  --     -- ssyt.irbs_cert.irb_inductive'_out_row],
  
  -- rw ssyt.irbs_cert.irb_inductive'_entry_eq_self_of_gt_row,
  
  -- { apply ssyt.irbs_cert.irb_inductive'_entry_eq_of_eq_mid,
  --     { exact congr_arg nat.pred hi' },
  --     { change T' _ _ = T _ _, rw [hi', hj, eq_row_mid _ _ ⟨hi''', by refl⟩] },
  --     { intros i' j' hij', 
  --       rw eq_cell _ _ ⟨hij'.1, hij'.2.trans (nat.pred_le _)⟩ },
  --     { intros i' j' hij',
  --       have key : i' < h.i,
  --         apply lt_of_le_of_lt hij'.2,
  --         apply nat.pred_lt (ne_of_gt _),
  --         apply lt_of_le_of_lt (nat.zero_le _) hi''',
  --       rw [h.irbs_entry_eq_of_ne_row (ne_of_lt key), 
  --           h'.irbs_entry_eq_of_ne_row (ne_of_lt _)],
  --       apply eq_row_mid _ _ ⟨hij'.1, le_of_lt key⟩,
  --       rw hi', exact key },
  --     { exact ⟨hi''.1, nat.le_pred_of_lt h_1⟩ }
  --  },
  -- { repeat {rw [ssyt.irbs_cert.irb_inductive_entry_eq_self_of_gt_row,
  --               ssyt.irbs_cert.irbs_entry]},
  --   rw [hi', hval, hj, eq_row_mid _ _ hi''],
  --   all_goals { change nat.pred _ < i, rw h_1 }, rw hi',
  --   all_goals { apply nat.pred_lt (ne_of_gt _),
  --               apply lt_of_le_of_lt (nat.zero_le _) hi''' }
  -- },
end


-- can the induction be turned inside out here?
-- currently it is irb_inductive(T,n) = irb_inductive(T.next, n-1),
-- that is, do 1 step, then do by induction.
-- can it be changed to irb_inductive = irb_inductive(T, n-1).next ?
-- probably easier to show inverse!


end inverse_row_bump'