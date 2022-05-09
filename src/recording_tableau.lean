import tactic
import row_bump

section recording_tableau

-- is this the right definition?
structure ssyt.rec_cert {μ : young_diagram} (B R : ssyt μ) := -- sorry
  (bumpval recval : ℕ)
  (rec_le : ∀ i' j' (cell' : (i', j') ∈ μ), R i' j' ≤ recval)
  (rec_eq_left : ∀ i' j' (cell' : (i', j') ∈ μ), R i' j' = recval →
                 j' < (B.row_bump bumpval).1.j)

end recording_tableau