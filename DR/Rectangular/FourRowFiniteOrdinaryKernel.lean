import DR.Certificates.OrdinaryColumnBlocks

/-!
# Weighted kernels for an iterated ordinary-label decomposition

The aggregate kernel may carry arbitrary coordinate weights. This is needed
when a second axis has already been averaged. A single ordinary label has
no fluctuation space, so that branch requires no positivity assumption on
the absent standard block.
-/

namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section
variable {ι κ γ : Type*} [Fintype ι] [Fintype κ] [Fintype γ] [DecidableEq γ]

omit [Fintype κ] [DecidableEq γ] in
theorem ordinaryColumn_fluctuation_eq_zero_of_card_one
    (hcard : Fintype.card γ = 1) (y : γ → κ → ℝ) (c : γ) :
    (fun i => y c i - (∑ a, y a i)/(Fintype.card γ : ℝ)) = 0 := by
  have hs : Subsingleton γ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  funext i
  have he : (∑ a, y a i) = y c i := by
    calc
      _ = ∑ _a : γ, y c i := by
        apply Finset.sum_congr rfl
        intro a _
        exact congrArg (fun b => y b i) (hs.elim a c)
      _ = _ := by simp [hcard]
  simp [he, hcard]

theorem ordinaryColumnMatrix_posSemidef_of_card_one_or
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hA : A.IsSymm) (hD : D.IsSymm) (hO : O.IsSymm)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosSemidef)
    (hH : Fintype.card γ = 1 ∨ (D-O).PosSemidef) :
    (ordinaryColumnMatrix (γ := γ) A G D O).PosSemidef := by
  rcases hH with hcard | hH
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_iff_isSymm.mpr (ordinaryColumnMatrix_isSymm A G D O hA hD hO))
    intro v
    let x : ι → ℝ := fun i => v (.inl i)
    let y : γ → κ → ℝ := fun c j => v (.inr (c,j))
    have hv : Sum.elim x (fun q : γ × κ => y q.1 q.2) = v := by
      funext p
      cases p <;> rfl
    have hz (c : γ) : quadraticValue (D-O)
        (fun j => y c j-(∑ a, y a j)/Fintype.card γ) = 0 := by
      rw [ordinaryColumn_fluctuation_eq_zero_of_card_one hcard y c]
      simp [quadraticValue]
    have he := quadraticValue_ordinaryColumn_decomposition A G D O x y hell
    simp only [hz, Finset.sum_const_zero, add_zero] at he
    have hb : 0 ≤ quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ))
        (Sum.elim x (fun j => ∑ c, y c j)) := by
      simpa only [quadraticValue_eq_dotProduct, star_trivial] using
        hB.dotProduct_mulVec_nonneg (Sum.elim x (fun j => ∑ c, y c j))
    have hp : 0 ≤ quadraticValue (ordinaryColumnMatrix A G D O)
        (Sum.elim x (fun q => y q.1 q.2)) := he.symm ▸ hb
    simpa only [hv, quadraticValue_eq_dotProduct, star_trivial] using hp
  · exact ordinaryColumnMatrix_posSemidef A G D O hA hD hO hell hB hH

/-- The weighted aggregate kernel transports through every signed coordinate,
including zero weights and the single-label branch. -/
theorem quadraticValue_ordinaryColumn_weighted_kernel
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosSemidef)
    (hH : Fintype.card γ = 1 ∨ (D-O).PosDef)
    (v : ι → ℝ) (w : κ → ℝ)
    (hker : ∀ x : ι → ℝ, ∀ z : κ → ℝ,
      quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ)) (Sum.elim x z) = 0 ↔
        ∃ t : ℝ, (∀ i, x i = t*v i) ∧ ∀ j, z j = Fintype.card γ*(t*w j))
    (x : ι → ℝ) (y : γ → κ → ℝ) :
    quadraticValue (ordinaryColumnMatrix A G D O) (Sum.elim x (fun q => y q.1 q.2)) = 0 ↔
      ∃ t : ℝ, (∀ i, x i = t*v i) ∧ ∀ c j, y c j = t*w j := by
  let z : κ → ℝ := fun i => ∑ c, y c i
  let f : γ → κ → ℝ := fun c i => y c i-z i/Fintype.card γ
  have hB0 : 0 ≤ quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ))
      (Sum.elim x z) := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      hB.dotProduct_mulVec_nonneg (Sum.elim x z)
  have hH0 (c : γ) : 0 ≤ quadraticValue (D-O) (f c) := by
    rcases hH with hcard | hp
    · have hz : f c = 0 := ordinaryColumn_fluctuation_eq_zero_of_card_one hcard y c
      simp [hz, quadraticValue]
    · simpa only [quadraticValue_eq_dotProduct, star_trivial] using
        hp.posSemidef.dotProduct_mulVec_nonneg (f c)
  have hzero (c : γ) (hle : quadraticValue (D-O) (f c) ≤ 0) : f c = 0 := by
    rcases hH with hcard | hp
    · exact ordinaryColumn_fluctuation_eq_zero_of_card_one hcard y c
    · by_contra hne
      have hpos : 0 < quadraticValue (D-O) (f c) := by
        simpa only [quadraticValue_eq_dotProduct, star_trivial] using hp.dotProduct_mulVec_pos hne
      linarith
  rw [quadraticValue_ordinaryColumn_decomposition A G D O x y hell]
  change quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ)) (Sum.elim x z) +
    (∑ c, quadraticValue (D-O) (f c)) = 0 ↔ _
  constructor
  · intro heq
    have hs : 0 ≤ ∑ c, quadraticValue (D-O) (f c) := Finset.sum_nonneg fun c _ => hH0 c
    have hbz : quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ))
        (Sum.elim x z) = 0 := by linarith
    obtain ⟨t, hxt, hzt⟩ := (hker x z).mp hbz
    refine ⟨t, hxt, ?_⟩
    intro c j
    have hle : quadraticValue (D-O) (f c) ≤ 0 := by
      have hsingle := Finset.single_le_sum (fun a _ => hH0 a) (Finset.mem_univ c)
      linarith
    have hj := congrFun (hzero c hle) j
    change y c j-z j/Fintype.card γ = 0 at hj
    rw [hzt j, mul_div_cancel_left₀ (t*w j) hell] at hj
    exact sub_eq_zero.mp hj
  · rintro ⟨t, hxt, hyt⟩
    have hzt (j : κ) : z j = (Fintype.card γ : ℝ)*(t*w j) := by
      simp only [z, hyt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hf (c : γ) : f c = 0 := by
      funext j
      dsimp [f]
      rw [hyt c j, hzt j, mul_div_cancel_left₀ (t*w j) hell, sub_self]
    rw [(hker x z).mpr ⟨t,hxt,hzt⟩]
    simp only [hf, quadraticValue, Pi.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero]

/-- Strict positivity also preserves the absent-standard-sector branch. -/
theorem ordinaryColumnMatrix_posDef_of_card_one_or
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hA : A.IsSymm) (hD : D.IsSymm) (hO : O.IsSymm)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosDef)
    (hH : Fintype.card γ = 1 ∨ (D-O).PosDef) :
    (ordinaryColumnMatrix (γ := γ) A G D O).PosDef := by
  have hfull := ordinaryColumnMatrix_posSemidef_of_card_one_or A G D O hA hD hO hell
    hB.posSemidef (hH.imp_right Matrix.PosDef.posSemidef)
  have hker (x : ι → ℝ) (z : κ → ℝ) :
      quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ)) (Sum.elim x z) = 0 ↔
        ∃ t : ℝ, (∀ i, x i = t*(0 : ℝ)) ∧ ∀ j, z j = Fintype.card γ*(t*(0 : ℝ)) := by
    constructor
    · intro hz
      have he : Sum.elim x z = 0 := by
        by_contra hne
        have hp : 0 < quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ))
            (Sum.elim x z) := by
          simpa only [quadraticValue_eq_dotProduct, star_trivial] using
            hB.dotProduct_mulVec_pos hne
        linarith
      refine ⟨0, ?_, ?_⟩
      · intro i
        simpa using congrFun he (.inl i)
      · intro j
        simpa using congrFun he (.inr j)
    · rintro ⟨t, hx, hz⟩
      have he : Sum.elim x z = 0 := by
        funext p
        cases p with
        | inl i => simpa using hx i
        | inr j => simpa using hz j
      simp [he, quadraticValue]
  have hk := quadraticValue_ordinaryColumn_weighted_kernel A G D O hell hB.posSemidef hH
    (fun _ => 0) (fun _ => 0) hker
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hfull.1
  intro v hne
  have hq : 0 ≤ quadraticValue (ordinaryColumnMatrix (γ := γ) A G D O) v := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using hfull.dotProduct_mulVec_nonneg v
  have hp : 0 < quadraticValue (ordinaryColumnMatrix (γ := γ) A G D O) v := by
    by_contra hn
    have hz : quadraticValue (ordinaryColumnMatrix (γ := γ) A G D O) v = 0 :=
      le_antisymm (not_lt.mp hn) hq
    have hv : Sum.elim (fun i => v (.inl i)) (fun q : γ × κ => v (.inr q)) = v := by
      funext p
      cases p <;> rfl
    have he : quadraticValue (ordinaryColumnMatrix A G D O)
        (Sum.elim (fun i => v (.inl i)) (fun q : γ × κ => v (.inr q))) = 0 := by
      rw [hv]
      exact hz
    obtain ⟨t, hx, hy⟩ := (hk (fun i => v (.inl i)) (fun c j => v (.inr (c,j)))).mp he
    apply hne
    funext p
    cases p with
    | inl i => simpa using hx i
    | inr q => simpa using hy q.1 q.2
  simpa only [quadraticValue_eq_dotProduct, star_trivial] using hp

end
end DittertRybin.Certificates
