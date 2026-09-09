import DR.Certificates.FiniteK3OrdinaryKernel

/-! Canonical finite indexing for the small-block criterion. The principal
matrix is exactly the first m*k+m-1 coordinates of the flattened aggregate. -/

namespace DittertRybin.Certificates
open scoped BigOperators

theorem finiteK3AggregateKernelFlat_apply {R : Type*} [One R]
    (m k : ℕ) (ell : R) (i : Fin (m*k+m)) :
    finiteK3AggregateKernelFlat m k ell i = if i.val < m*k then 1 else ell := by
  obtain ⟨a, rfl⟩ := (finiteK3AggregateEquiv m k).surjective i
  rcases a with ⟨r,c⟩ | r
  · simp only [finiteK3AggregateKernelFlat, Function.comp_apply, Equiv.symm_apply_apply,
      finiteK3AggregateKernel, Sum.elim_inl]
    change 1 = if (finProdFinEquiv (r,c)).val < m*k then 1 else ell
    rw [if_pos (finProdFinEquiv (r,c)).isLt]
  · simp only [finiteK3AggregateKernelFlat, Function.comp_apply, Equiv.symm_apply_apply,
      finiteK3AggregateKernel, Sum.elim_inr]
    change ell = if m*k+r.val < m*k then 1 else ell
    rw [if_neg (by omega)]

theorem finiteK3OrdinaryBFlat_cast {m k : ℕ} (coeff : Fin 93 → ℚ)
    (e f : Fin m × Fin k) (ell : ℚ) :
    (finiteK3OrdinaryBFlat coeff e f ell).map (fun q : ℚ => (q : ℝ)) =
      finiteK3OrdinaryBFlat (fun i => (coeff i : ℝ)) e f (ell : ℝ) := by
  simp only [finiteK3OrdinaryBFlat, ← Matrix.submatrix_map, finiteK3OrdinaryB_cast]

theorem finiteK3OrdinaryB0_cast {m k : ℕ} (coeff : Fin 93 → ℚ)
    (e f : Fin m × Fin k) (ell : ℚ) :
    (finiteK3OrdinaryB0 coeff e f ell).map (fun q : ℚ => (q : ℝ)) =
      finiteK3OrdinaryB0 (fun i => (coeff i : ℝ)) e f (ell : ℝ) := by
  simp only [finiteK3OrdinaryB0, ← Matrix.submatrix_map, finiteK3OrdinaryBFlat_cast]

theorem finiteK3AggregateKernelFlat_cast (m k : ℕ) (ell : ℚ) (i : Fin (m*k+m)) :
    ((finiteK3AggregateKernelFlat m k ell i : ℚ) : ℝ) =
      finiteK3AggregateKernelFlat m k (ell : ℝ) i := by
  by_cases hi : i.val < m*k <;> simp [finiteK3AggregateKernelFlat_apply, hi]

def finiteK3AggregatePrincipalEquiv (m k : ℕ) (hm : 0 < m) :
    Fin ((m*k+m-1)+1) ≃ ((Fin m × Fin k) ⊕ Fin m) :=
  (finCongr (by omega : (m*k+m-1)+1 = m*k+m)).trans (finiteK3AggregateEquiv m k).symm

theorem finiteK3AggregatePrincipalEquiv_castSucc (m k : ℕ) (hm : 0 < m)
    (i : Fin (m*k+m-1)) :
    finiteK3AggregatePrincipalEquiv m k hm i.castSucc =
      (finiteK3AggregateEquiv m k).symm (Fin.castLE (Nat.sub_le (m*k+m) 1) i) := by
  apply congrArg (finiteK3AggregateEquiv m k).symm
  exact Fin.ext rfl

/-- The literal flat kernel check is the same as the aggregate kernel equation. -/
theorem finiteK3OrdinaryB_kernel_of_flat {m k : ℕ} (coeff : Fin 93 → ℝ)
    (e f : Fin m × Fin k) (ell : ℝ)
    (hflat : (finiteK3OrdinaryBFlat coeff e f ell).mulVec
      (finiteK3AggregateKernelFlat m k ell) = 0) :
    (finiteK3OrdinaryB coeff e f ell).mulVec (finiteK3AggregateKernel ell) = 0 := by
  have h := mulVec_kernel_submatrix_equiv (finiteK3OrdinaryBFlat coeff e f ell)
    (finiteK3AggregateKernelFlat m k ell) hflat (finiteK3AggregateEquiv m k)
  have hmatrix : (finiteK3OrdinaryBFlat coeff e f ell).submatrix
      (finiteK3AggregateEquiv m k) (finiteK3AggregateEquiv m k) =
        finiteK3OrdinaryB coeff e f ell := by
    ext i j
    simp only [finiteK3OrdinaryBFlat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hvector : finiteK3AggregateKernelFlat m k ell ∘ finiteK3AggregateEquiv m k =
      finiteK3AggregateKernel ell := by
    funext i
    simp only [finiteK3AggregateKernelFlat, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hmatrix, hvector] at h
  exact h

/-- The two actual finite positive-definite blocks and flat kernel checks suffice
for the full seed, with every real vector and every closed-boundary support. -/
theorem finiteK3Ordinary_flat_criterion {m k ell : ℕ} (hm : 0 < m) (hell : 0 < ell)
    (coeff : Fin 93 → ℝ) (e f : Fin m × Fin k)
    (hkernel : (finiteK3OrdinaryBFlat coeff e f (ell : ℝ)).mulVec
      (finiteK3AggregateKernelFlat m k (ell : ℝ)) = 0)
    (hB0 : (finiteK3OrdinaryB0 coeff e f (ell : ℝ)).PosDef)
    (hH : (finiteK3OrdinaryH coeff e f).PosDef) :
    Matrix.PosSemidef (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2) :
      Matrix (Fin m × (Fin k ⊕ Fin ell)) (Fin m × (Fin k ⊕ Fin ell)) ℝ) ∧
    ∀ p : Fin m × (Fin k ⊕ Fin ell) → ℝ,
      quadraticValue (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)) p = 0 ↔
        ∃ t : ℝ, ∀ a, p a = t := by
  have hk := finiteK3OrdinaryB_kernel_of_flat coeff e f (ell : ℝ) hkernel
  have hp : ((finiteK3OrdinaryB coeff e f (ell : ℝ)).submatrix
      (fun i : Fin (m*k+m-1) => finiteK3AggregatePrincipalEquiv m k hm i.castSucc)
      (fun i : Fin (m*k+m-1) => finiteK3AggregatePrincipalEquiv m k hm i.castSucc)).PosDef := by
    simpa only [finiteK3AggregatePrincipalEquiv_castSucc, finiteK3OrdinaryB0,
      finiteK3OrdinaryBFlat, Matrix.submatrix_submatrix, Function.comp_def] using hB0
  refine finiteK3Ordinary_kernel_criterion coeff e f ?_
    (finiteK3AggregatePrincipalEquiv m k hm) ?_ ?_ hH
  · simpa only [Fintype.card_fin] using (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell) : (ell : ℝ) ≠ 0)
  · simpa only [Fintype.card_fin] using hk
  · simpa only [Fintype.card_fin] using hp

end DittertRybin.Certificates
