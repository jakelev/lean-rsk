import tactic
import row_insertion
import inverse_row_insertion

section irbs_rbs

lemma ssyt.rbs_cert.irbc_aux
  {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) 
  (cell : (h.i, h.j) ∈ μ) :
  ∃ j, ((h.i, j) ∈ μ ∧ (h.rbs cell) h.i j < h.out) :=
  ⟨h.j, ⟨cell, by { rw [h.rbs_entry, if_pos rfl], 
                    exact h.out_lt_val cell }⟩⟩

lemma ssyt.rbs_cert.irbc_eq_j
  {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) 
  (cell : (h.i, h.j) ∈ μ) :
  (h.rbs cell).irbc (h.irbc_aux cell) = h.j :=
begin
  rw ssyt.irbc_eq_iff, split, exact cell,
  split,
  { rw [h.rbs_entry, if_pos rfl], exact h.out_lt_val cell },
  { intros j' hj' cell',
    rw [h.rbs_entry, if_neg],
    apply T.row_weak hj' cell',
    exact λ hij, (ne_of_lt hj').symm (prod.mk.inj_left h.i hij) }
end

@[simps]
def ssyt.rbs_cert.to_irbs_cert 
  {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) 
  (cell : (h.i, h.j) ∈ μ) : (h.rbs cell).irbs_cert :=
{ i := h.i,
  val := h.out,
  exists_lt := h.irbc_aux cell,
  down := λ i' hi' cell', begin
    rw h.irbc_eq_j at ⊢ cell',
    rw h.rbs_entry_eq_of_ne_row _ (ne_of_lt hi').symm,
    exact T.col_strict hi' cell',
  end,
}

lemma ssyt.rbs_cert.to_irbs_cert_j 
  {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert)
  (cell : (h.i, h.j) ∈ μ) : (h.to_irbs_cert cell).j = h.j := h.irbc_eq_j cell

lemma ssyt.rbs_cert.irbs_rbs
  {μ : young_diagram} {T : ssyt μ} (h : T.rbs_cert) 
  (cell : (h.i, h.j) ∈ μ) : (h.to_irbs_cert cell).irbs = T :=
begin
  ext i j, repeat {rw ssyt.to_entry},
  rw [ssyt.irbs_cert.irbs_entry, h.to_irbs_cert_i, h.to_irbs_cert_val,
      h.to_irbs_cert_j],
  split_ifs,
    { cases h_1, refl },
    { rw [h.rbs_entry, if_neg h_1] }
end

end irbs_rbs

section rbs_irbs

lemma ssyt.irbs_cert.rbc_eq_j
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) :
  h.irbs.rbc h.i h.out = h.j :=
begin
  rw ssyt.rbc_eq_iff, split,
  { intro cell,
    rw [h.irbs_entry, if_pos rfl], exact h.out_lt_val },
  { intros j' hj', rw [h.irbs_entry, if_neg],
    exact ⟨μ.nw_of (le_refl _) (le_of_lt hj') h.cell, T.row_weak hj' h.cell⟩,
    exact λ hij, (ne_of_lt hj') (prod.mk.inj_left h.i hij) }
end

@[simps]
def ssyt.irbs_cert.to_rbs_cert
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : h.irbs.rbs_cert :=
{ i := h.i,
  val := h.out,
  cell_up := λ i hi, h.rbc_eq_j.symm ▸ μ.nw_of (le_of_lt hi) (by refl) h.cell,
  up := λ i hi, begin
    rw [h.rbc_eq_j, h.irbs_entry, if_neg],
    exact T.col_strict hi h.cell,
    exact λ hij, (ne_of_lt hi) (prod.mk.inj_right h.j hij),
  end
}

lemma ssyt.irbs_cert.to_rbs_cert_j
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : 
h.to_rbs_cert.j = h.j := h.rbc_eq_j

lemma ssyt.irbs_cert.to_rbs_cert_cell
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : 
(h.to_rbs_cert.i, h.to_rbs_cert.j) ∈ μ := h.to_rbs_cert_j.symm ▸ h.cell

lemma ssyt.irbs_cert.rbs_irbs
  {μ : young_diagram} {T : ssyt μ} (h : T.irbs_cert) : 
  h.to_rbs_cert.rbs h.to_rbs_cert_cell = T :=
begin
  ext i j, repeat {rw ssyt.to_entry},
  rw [ssyt.rbs_cert.rbs_entry, h.to_rbs_cert_i, h.to_rbs_cert_val,
      h.to_rbs_cert_j],
  split_ifs,
    { cases h_1, refl },
    { rw [h.irbs_entry, if_neg h_1] }
end

end rbs_irbs