import DR.Certificates.FiniteK3OrdinaryFlat
import DR.Certificates.ConstantKernel

/-! Transport the checked small blocks to actual Fin m × Fin n cell matrices.
The first k columns are distinguished and the remaining n-k columns are
ordinary. Rational block checks are cast through proved entry identities. -/

namespace DittertRybin.Certificates
open scoped BigOperators

def finiteK3ColumnSplitEquiv (k n : ℕ) (hkn : k ≤ n) :
    (Fin k ⊕ Fin (n-k)) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega : k+(n-k) = n))

theorem finiteK3ColumnSplitEquiv_left (k n : ℕ) (hkn : k ≤ n) (i : Fin k) :
    finiteK3ColumnSplitEquiv k n hkn (.inl i) = Fin.castLE hkn i := by
  exact Fin.ext rfl

/-- The split-column strict criterion applies to the literal rectangular seed. -/
theorem finiteK3Ordinary_rectangle_criterion {m k n : ℕ} (hm : 0 < m) (hkn : k < n)
    (coeff : Fin 93 → ℝ) (e f : Fin m × Fin k)
    (hkernel : (finiteK3OrdinaryBFlat coeff e f ((n-k : ℕ) : ℝ)).mulVec
      (finiteK3AggregateKernelFlat m k ((n-k : ℕ) : ℝ)) = 0)
    (hB0 : (finiteK3OrdinaryB0 coeff e f ((n-k : ℕ) : ℝ)).PosDef)
    (hH : (finiteK3OrdinaryH coeff e f).PosDef) :
    Matrix.PosSemidef (finiteK3Entry coeff (e.1,e.2.castLE hkn.le) (f.1,f.2.castLE hkn.le)) ∧
    ∀ p : Fin m × Fin n → ℝ,
      quadraticValue (finiteK3Entry coeff (e.1,e.2.castLE hkn.le) (f.1,f.2.castLE hkn.le)) p = 0 ↔
        ∃ t : ℝ, ∀ a, p a = t := by
  have hs := finiteK3Ordinary_flat_criterion hm (Nat.sub_pos_of_lt hkn) coeff e f hkernel hB0 hH
  have h := finiteK3Entry_criterion_equiv coeff (Equiv.refl (Fin m))
    (finiteK3ColumnSplitEquiv k n hkn.le) (e.1,Sum.inl e.2) (f.1,Sum.inl f.2) hs.1 hs.2
  simpa only [Equiv.refl_apply, finiteK3ColumnSplitEquiv_left] using h

/-- Exact rational checks retain their actual real-matrix meaning. -/
theorem finiteK3Ordinary_rational_rectangle_criterion {m k n : ℕ}
    (hm : 0 < m) (hkn : k < n) (coeff : Fin 93 → ℚ) (e f : Fin m × Fin k)
    (hkernel : ∀ i, (∑ j, finiteK3OrdinaryBFlat coeff e f ((n-k : ℕ) : ℚ) i j *
      finiteK3AggregateKernelFlat m k ((n-k : ℕ) : ℚ) j) = 0)
    (hB0 : ((finiteK3OrdinaryB0 coeff e f ((n-k : ℕ) : ℚ)).map
      (fun q : ℚ => (q : ℝ))).PosDef)
    (hH : ((finiteK3OrdinaryH coeff e f).map (fun q : ℚ => (q : ℝ))).PosDef) :
    Matrix.PosSemidef (finiteK3Entry (fun i => (coeff i : ℝ))
      (e.1,e.2.castLE hkn.le) (f.1,f.2.castLE hkn.le)) ∧
    ∀ p : Fin m × Fin n → ℝ,
      quadraticValue (finiteK3Entry (fun i => (coeff i : ℝ))
        (e.1,e.2.castLE hkn.le) (f.1,f.2.castLE hkn.le)) p = 0 ↔
        ∃ t : ℝ, ∀ a, p a = t := by
  rw [finiteK3OrdinaryB0_cast] at hB0
  rw [finiteK3OrdinaryH_cast] at hH
  have hk : ((finiteK3OrdinaryBFlat coeff e f ((n-k : ℕ) : ℚ)).map
      (fun q : ℚ => (q : ℝ))).mulVec
      (fun i => ((finiteK3AggregateKernelFlat m k ((n-k : ℕ) : ℚ) i : ℚ) : ℝ)) = 0 := by
    funext i
    change (∑ j, ((finiteK3OrdinaryBFlat coeff e f ((n-k : ℕ) : ℚ) i j : ℚ) : ℝ) *
      ((finiteK3AggregateKernelFlat m k ((n-k : ℕ) : ℚ) j : ℚ) : ℝ)) = 0
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hkernel i)
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero] using h
  have hv : (fun i => ((finiteK3AggregateKernelFlat m k ((n-k : ℕ) : ℚ) i : ℚ) : ℝ)) =
      finiteK3AggregateKernelFlat m k (((n-k : ℕ) : ℚ) : ℝ) := by
    funext i
    exact finiteK3AggregateKernelFlat_cast m k _ i
  rw [finiteK3OrdinaryBFlat_cast, hv] at hk
  simpa only [Rat.cast_natCast] using
    finiteK3Ordinary_rectangle_criterion hm hkn (fun i => (coeff i : ℝ)) e f hk hB0 hH

end DittertRybin.Certificates
