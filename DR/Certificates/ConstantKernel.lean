import DR.Certificates.PairNormalization
import DR.Certificates.FiniteK3Orbits

/-! Exact constant quadratic kernels are invariant under bijective reindexing,
and physical row/column relabeling preserves every finite-K3 coefficient role. -/

namespace DittertRybin.Certificates

theorem psd_constant_kernel_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι ι ℝ) (e : κ ≃ ι) (hQ : Q.PosSemidef)
    (hker : ∀ x : ι → ℝ, quadraticValue Q x = 0 ↔ ∃ t : ℝ, ∀ i, x i = t) :
    (Q.submatrix e e).PosSemidef ∧ ∀ x : κ → ℝ,
      quadraticValue (Q.submatrix e e) x = 0 ↔ ∃ t : ℝ, ∀ i, x i = t := by
  refine ⟨hQ.submatrix e, fun x => ?_⟩
  rw [quadraticValue_submatrix_equiv, hker]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun i => by simpa using ht (e i)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, fun i => ht (e.symm i)⟩

/-- Actual row and column equivalences transport PSD and the exact constant kernel. -/
theorem finiteK3Entry_criterion_equiv {ρ δ ρ' δ' : Type*}
    [Fintype ρ] [Fintype δ] [Fintype ρ'] [Fintype δ']
    [DecidableEq ρ] [DecidableEq δ] [DecidableEq ρ'] [DecidableEq δ']
    (coeff : Fin 93 → ℝ) (r : ρ ≃ ρ') (c : δ ≃ δ') (e f : ρ × δ)
    (hQ : Matrix.PosSemidef (finiteK3Entry coeff e f))
    (hker : ∀ x : ρ × δ → ℝ, quadraticValue (finiteK3Entry coeff e f) x = 0 ↔
      ∃ t : ℝ, ∀ i, x i = t) :
    Matrix.PosSemidef (finiteK3Entry coeff (r e.1,c e.2) (r f.1,c f.2)) ∧
    ∀ x : ρ' × δ' → ℝ,
      quadraticValue (finiteK3Entry coeff (r e.1,c e.2) (r f.1,c f.2)) x = 0 ↔
        ∃ t : ℝ, ∀ i, x i = t := by
  let E : (ρ × δ) ≃ (ρ' × δ') := Equiv.prodCongr r c
  have hm : (finiteK3Entry coeff (r e.1,c e.2) (r f.1,c f.2) :
      Matrix (ρ' × δ') (ρ' × δ') ℝ) =
      Matrix.submatrix (finiteK3Entry coeff e f : Matrix (ρ × δ) (ρ × δ) ℝ) E.symm E.symm := by
    ext a b
    have ha : (r (E.symm a).1,c (E.symm a).2) = a := E.apply_symm_apply a
    have hb : (r (E.symm b).1,c (E.symm b).2) = b := E.apply_symm_apply b
    have h := finiteK3Entry_map coeff r c r.injective c.injective e f (E.symm a) (E.symm b)
    rw [ha,hb] at h
    exact h
  have h := psd_constant_kernel_submatrix (finiteK3Entry coeff e f) E.symm hQ hker
  rw [← hm] at h
  exact h

end DittertRybin.Certificates
