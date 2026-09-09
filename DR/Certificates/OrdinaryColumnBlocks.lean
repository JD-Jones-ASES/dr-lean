import DR.Certificates.Gram
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact reduction of interchangeable ordinary columns

For a distinguished block A and ell identical ordinary columns, the full
quadratic form reduces to one aggregate block B and ell centered copies of
H = D - O. This is the dimension-independent matrix step in the finite K=3
certificates. No polynomial identity or numerical positive-definiteness test
is assumed by this reduction.
-/

namespace DittertRybin.Certificates

open scoped BigOperators

noncomputable section

variable {ι κ γ : Type*}

/-- The actual matrix on distinguished cells and ordinary-column cells. -/
def ordinaryColumnMatrix [DecidableEq γ] (A : Matrix ι ι ℝ)
    (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ) :
    Matrix (ι ⊕ (γ × κ)) (ι ⊕ (γ × κ)) ℝ
  | .inl i, .inl j => A i j
  | .inl i, .inr q => G i q.2
  | .inr p, .inl j => G j p.2
  | .inr p, .inr q => if p.1 = q.1 then D p.2 q.2 else O p.2 q.2

/-- The reduced lower-right block includes the essential factor 1 / ell. -/
def ordinaryAggregateMatrix (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ)
    (D O : Matrix κ κ ℝ) (ell : ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ
  | .inl i, .inl j => A i j
  | .inl i, .inr j => G i j
  | .inr i, .inl j => G j i
  | .inr i, .inr j => O i j + (D i j - O i j) / ell

theorem ordinaryAggregateMatrix_entry (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ)
    (D O : Matrix κ κ ℝ) (ell : ℝ) (hell : ell ≠ 0) (i j : κ) :
    ordinaryAggregateMatrix A G D O ell (.inr i) (.inr j) =
      (D i j + (ell - 1) * O i j) / ell := by
  dsimp [ordinaryAggregateMatrix]
  field_simp
  ring

variable [Fintype ι] [Fintype κ] [Fintype γ]

theorem sum_centered_mul (u v : γ → ℝ) (hell : (Fintype.card γ : ℝ) ≠ 0) :
    (∑ c, (u c - (∑ a, u a) / Fintype.card γ) *
      (v c - (∑ a, v a) / Fintype.card γ)) =
      (∑ c, u c * v c) - (∑ c, u c) * (∑ c, v c) / Fintype.card γ := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem quadraticValue_centered_columns (H : Matrix κ κ ℝ) (y : γ → κ → ℝ)
    (hell : (Fintype.card γ : ℝ) ≠ 0) :
    (∑ c, quadraticValue H (fun i => y c i - (∑ a, y a i) / Fintype.card γ)) =
      (∑ c, quadraticValue H (y c)) -
        quadraticValue H (fun i => ∑ c, y c i) / Fintype.card γ := by
  unfold quadraticValue
  calc
    _ = ∑ i, ∑ j, ∑ c, (y c i - (∑ a, y a i) / Fintype.card γ) * H i j *
        (y c j - (∑ a, y a j) / Fintype.card γ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ((∑ c, y c i * H i j * y c j) -
        (∑ c, y c i) * H i j * (∑ c, y c j) / Fintype.card γ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = H i j * ∑ c, (y c i - (∑ a, y a i) / Fintype.card γ) *
            (y c j - (∑ a, y a j) / Fintype.card γ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          ring
        _ = _ := by
          rw [sum_centered_mul _ _ hell, mul_sub, Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl
            intro c _
            ring
          · ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
      congr 1
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

theorem sum_column_cross (G : Matrix ι κ ℝ) (x : ι → ℝ) (y : γ → κ → ℝ) :
    (∑ i, ∑ c, ∑ j, x i * G i j * y c j) =
      ∑ i, ∑ j, x i * G i j * (∑ c, y c j) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

theorem sum_ordinary_block [DecidableEq γ] (D O : Matrix κ κ ℝ)
    (y : γ → κ → ℝ) :
    (∑ c, ∑ i, ∑ d, ∑ j, y c i * (if c = d then D i j else O i j) * y d j) =
      (∑ c, quadraticValue (D - O) (y c)) +
        quadraticValue O (fun i => ∑ c, y c i) := by
  have hentry (c d : γ) (i j : κ) :
      (if c = d then D i j else O i j) =
        (if c = d then D i j - O i j else 0) + O i j := by
    split_ifs <;> ring
  simp_rw [hentry, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  · calc
      _ = ∑ i, ∑ c, ∑ d, ∑ j, y c i * O i j * y d j := Finset.sum_comm
      _ = ∑ i, ∑ c, ∑ j, ∑ d, y c i * O i j * y d j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro c _
        exact Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ c, ∑ d, y c i * O i j * y d j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        simp only [quadraticValue, ← Finset.mul_sum, ← Finset.sum_mul]

theorem quadraticValue_ordinaryColumnMatrix [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (x : ι → ℝ) (y : γ → κ → ℝ) :
    quadraticValue (ordinaryColumnMatrix A G D O)
        (Sum.elim x (fun q => y q.1 q.2)) =
      quadraticValue A x + 2 * (∑ i, ∑ j, x i * G i j * (∑ c, y c j)) +
        (∑ c, quadraticValue (D - O) (y c)) +
        quadraticValue O (fun i => ∑ c, y c i) := by
  simp only [quadraticValue, Fintype.sum_sum_type, Fintype.sum_prod_type,
    ordinaryColumnMatrix, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
  have hcross : (∑ c, ∑ i, ∑ j, y c i * G j i * x j) =
      ∑ i, ∑ j, x i * G i j * (∑ c, y c j) := by
    calc
      _ = ∑ c, ∑ j, ∑ i, y c i * G j i * x j := by
        apply Finset.sum_congr rfl
        intro c _
        exact Finset.sum_comm
      _ = ∑ j, ∑ c, ∑ i, y c i * G j i * x j := Finset.sum_comm
      _ = ∑ j, ∑ i, ∑ c, y c i * G j i * x j := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
      _ = _ := by
        simp only [← Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [sum_column_cross, hcross, sum_ordinary_block]
  simp only [quadraticValue]
  ring

theorem quadraticValue_ordinaryAggregateMatrix
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (ell : ℝ) (x : ι → ℝ) (z : κ → ℝ) :
    quadraticValue (ordinaryAggregateMatrix A G D O ell) (Sum.elim x z) =
      quadraticValue A x + 2 * (∑ i, ∑ j, x i * G i j * z j) +
        quadraticValue O z + quadraticValue (D - O) z / ell := by
  simp only [quadraticValue, Fintype.sum_sum_type, ordinaryAggregateMatrix,
    Sum.elim_inl, Sum.elim_inr, mul_add, add_mul, Finset.sum_add_distrib,
    Matrix.sub_apply]
  have hcross : (∑ i, ∑ j, z i * G j i * x j) = ∑ j, ∑ i, x j * G j i * z i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcross]
  have hdiv : (∑ i, ∑ j, z i * ((D i j - O i j) / ell) * z j) =
      (∑ i, ∑ j, z i * (D i j - O i j) * z j) / ell := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdiv]
  ring

/-- Exact ordinary-column decomposition, for every signed vector and nonempty
ordinary-column type. No symmetry or positivity hypothesis is needed for the identity. -/
theorem quadraticValue_ordinaryColumn_decomposition [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (x : ι → ℝ) (y : γ → κ → ℝ) (hell : (Fintype.card γ : ℝ) ≠ 0) :
    quadraticValue (ordinaryColumnMatrix A G D O)
        (Sum.elim x (fun q => y q.1 q.2)) =
      quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ))
        (Sum.elim x (fun i => ∑ c, y c i)) +
      ∑ c, quadraticValue (D - O) (fun i => y c i - (∑ a, y a i) / Fintype.card γ) := by
  rw [quadraticValue_ordinaryColumnMatrix, quadraticValue_ordinaryAggregateMatrix,
    quadraticValue_centered_columns _ _ hell]
  ring

theorem quadraticValue_ordinaryColumn_nonneg [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosSemidef)
    (hH : (D - O).PosSemidef) (x : ι → ℝ) (y : γ → κ → ℝ) :
    0 ≤ quadraticValue (ordinaryColumnMatrix A G D O)
      (Sum.elim x (fun q => y q.1 q.2)) := by
  rw [quadraticValue_ordinaryColumn_decomposition A G D O x y hell]
  apply add_nonneg
  · simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      hB.dotProduct_mulVec_nonneg (Sum.elim x (fun i => ∑ c, y c i))
  · apply Finset.sum_nonneg
    intro c _
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      hH.dotProduct_mulVec_nonneg (fun i => y c i - (∑ a, y a i) / Fintype.card γ)

omit [Fintype ι] [Fintype κ] [Fintype γ] in
theorem ordinaryColumnMatrix_isSymm [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hA : A.IsSymm) (hD : D.IsSymm) (hO : O.IsSymm) :
    (ordinaryColumnMatrix (γ := γ) A G D O).IsSymm := by
  apply Matrix.IsSymm.ext
  intro p q
  cases p with
  | inl i => cases q with
    | inl j => exact hA.apply i j
    | inr q => rfl
  | inr p => cases q with
    | inl j => rfl
    | inr q =>
      dsimp [ordinaryColumnMatrix]
      by_cases h : p.1 = q.1
      · rw [if_pos h, if_pos h.symm]
        exact hD.apply p.2 q.2
      · rw [if_neg h, if_neg (Ne.symm h)]
        exact hO.apply p.2 q.2

/-- The two small PSD blocks imply positivity of the entire physical matrix. -/
theorem ordinaryColumnMatrix_posSemidef [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hA : A.IsSymm) (hD : D.IsSymm) (hO : O.IsSymm)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosSemidef)
    (hH : (D - O).PosSemidef) :
    (ordinaryColumnMatrix (γ := γ) A G D O).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (ordinaryColumnMatrix_isSymm A G D O hA hD hO))
  intro v
  have hv : Sum.elim (fun i => v (.inl i)) (fun q : γ × κ => v (.inr q)) = v := by
    funext p
    cases p <;> rfl
  have h := quadraticValue_ordinaryColumn_nonneg A G D O hell hB hH
    (fun i => v (.inl i)) (fun c j => v (.inr (c,j)))
  simpa only [hv, quadraticValue_eq_dotProduct, star_trivial] using h

/-- A strictly positive fluctuation block and the prescribed aggregate kernel
give exactly the constant vectors in the full quadratic kernel. The aggregate
kernel condition is supplied separately by the checked principal block. -/
theorem quadraticValue_ordinaryColumn_eq_zero_iff [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosSemidef)
    (hH : (D - O).PosDef)
    (hker : ∀ x : ι → ℝ, ∀ z : κ → ℝ,
      quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ)) (Sum.elim x z) = 0 ↔
        ∃ t : ℝ, (∀ i, x i = t) ∧ ∀ j, z j = Fintype.card γ * t)
    (x : ι → ℝ) (y : γ → κ → ℝ) :
    quadraticValue (ordinaryColumnMatrix A G D O) (Sum.elim x (fun q => y q.1 q.2)) = 0 ↔
      ∃ t : ℝ, (∀ i, x i = t) ∧ ∀ c j, y c j = t := by
  let z : κ → ℝ := fun i => ∑ c, y c i
  let w : γ → κ → ℝ := fun c i => y c i - z i / Fintype.card γ
  have hB0 : 0 ≤ quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ))
      (Sum.elim x z) := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      hB.dotProduct_mulVec_nonneg (Sum.elim x z)
  have hH0 (c : γ) : 0 ≤ quadraticValue (D - O) (w c) := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      hH.posSemidef.dotProduct_mulVec_nonneg (w c)
  rw [quadraticValue_ordinaryColumn_decomposition A G D O x y hell]
  change quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ)) (Sum.elim x z) +
    (∑ c, quadraticValue (D - O) (w c)) = 0 ↔ _
  constructor
  · intro heq
    have hsum0 : 0 ≤ ∑ c, quadraticValue (D - O) (w c) :=
      Finset.sum_nonneg fun c _ => hH0 c
    have hBzero : quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ))
        (Sum.elim x z) = 0 := by linarith
    obtain ⟨t, hxt, hzt⟩ := (hker x z).mp hBzero
    refine ⟨t, hxt, ?_⟩
    intro c j
    have hcle : quadraticValue (D - O) (w c) ≤ 0 := by
      have hsingle := Finset.single_le_sum (fun d _ => hH0 d) (Finset.mem_univ c)
      linarith
    have hw : w c = 0 := by
      by_contra hne
      have hpos : 0 < quadraticValue (D - O) (w c) := by
        simpa only [quadraticValue_eq_dotProduct, star_trivial] using
          hH.dotProduct_mulVec_pos hne
      linarith
    have hj := congrFun hw j
    change y c j - z j / Fintype.card γ = 0 at hj
    rw [hzt j, mul_div_cancel_left₀ t hell] at hj
    exact sub_eq_zero.mp hj
  · rintro ⟨t, hxt, hyt⟩
    have hzt (j : κ) : z j = (Fintype.card γ : ℝ) * t := by
      simp only [z, hyt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hw (c : γ) : w c = 0 := by
      funext j
      dsimp [w]
      rw [hyt c j, hzt j, mul_div_cancel_left₀ t hell, sub_self]
    rw [(hker x z).mpr ⟨t,hxt,hzt⟩]
    simp only [hw, quadraticValue, Pi.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero]

end

end DittertRybin.Certificates
