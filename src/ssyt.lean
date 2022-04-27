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

lemma ssyt.zeros {μ : young_diagram} (T : ssyt μ) : 
  ∀ {i j : ℕ}, (i, j) ∉ μ → T i j = 0 := T.zeros'

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
    change i1 = i2 at hi, change j1 < j2 at hj, subst i2,
    apply TT.val.row_weak hj hc',
  end,
  λ c c' hi hj, begin
    cases c with c hc, cases c with i1 j1,
    cases c' with c' hc', cases c' with i2 j2,
    change i1 < i2 at hi, change j1 = j2 at hj, subst j2,
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