import tactic
import row_bump
import inverse_row_bump

/-

Very preliminary -- see comments in inverse_row_bump.lean

-/

section irb_rbwf

-- irb_inductive' ∘ rbwf = id (start and end in row i)

def ssyt.rbs_cert.del_rbwf {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) :
  ssyt μ := 
(h.rbwf.2.del h.rbwf.1.to_inner).copy (young_diagram.inner_outer _)

def ssyt.irb_with_stopping :
  Π {μ : young_diagram} (T : ssyt μ) (c : μ.inner_corner)
  {end_after : ℕ} {i : ℕ} (hi : c.i = end_after + i),
  ssyt c.del × ℕ
| μ T c end_after 0 hi := ⟨T.del c, T c.i c.j⟩
| μ T c end_after (nat.succ n) hi := begin
  have key : c.i ≠ 0 := by convert nat.succ_ne_zero (end_after + n),
  have key2 : c.i.pred = end_after + n := 
    by rw [hi, nat.add_succ, nat.pred_succ],
  set out := (T.irbs_cert_of_inner_corner c key).irb_inductive' key2,
  exact ⟨out.2.1.irbs, out.2.1.out⟩,
end

def ssyt.irb_with_stopping'
  {μ : young_diagram} {c : μ.outer_corner} (T : ssyt c.add)
  {end_after : ℕ} {i : ℕ} (hi : c.i = end_after + i) :
  ssyt μ × ℕ :=
let out := T.irb_with_stopping c.to_inner hi in
⟨ssyt.copy out.1 (young_diagram.inner_outer c), out.2⟩

lemma ssyt.irb_rbwf :
  Π {μ : young_diagram} (T : ssyt μ) (h : T.rbs_cert)
  (hi : h.rbwf.1.i = h.i + (h.rbwf.1.i - h.i)),
    -- begin
    -- by rw [← nat.add_sub_assoc h.i_le_rbwf_corner,
    --       nat.add_sub_cancel_left]
    -- end),
  h.rbwf.2.irb_with_stopping' --h.i (h.rbwf.1.i - h.i)
    hi =
  -- (by rw [← nat.add_sub_assoc h.i_le_rbwf_corner,
  --         nat.add_sub_cancel_left] : h.rbwf.1.i = h.i + (h.rbwf.1.i - h.i)) =
  (T, h.val)
| μ T h hi :=
dite ((h.i, h.j) ∈ μ)
(λ cell, begin sorry
end)
(λ not_cell, begin sorry
end)

end irb_rbwf