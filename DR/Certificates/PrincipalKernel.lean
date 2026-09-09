import DR.Certificates.Gram
import DR.Certificates.PairNormalization

/-! A checked principal block and a nonvanishing known kernel vector determine
the entire quadratic kernel. The finite indexing equivalence is explicit, so
the omitted coordinate used by rational certificates remains reviewable. -/

namespace DittertRybin.Certificates
open scoped BigOperators

/-- Transport an actual matrix kernel equation through a finite indexing equivalence. -/
theorem mulVec_kernel_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι ι ℝ) (v : ι → ℝ) (hv : Q.mulVec v = 0) (e : κ ≃ ι) :
    (Q.submatrix e e).mulVec (v ∘ e) = 0 := by
  funext i
  change (∑ j, Q (e i) (e j) * v (e j)) = 0
  calc
    _ = ∑ j, Q (e i) j * v j := Equiv.sum_comp e (fun j => Q (e i) j * v j)
    _ = 0 := congrFun hv (e i)

/-- An explicit positive principal block gives PSD and the exact one-dimensional
quadratic kernel, including the zero vector. -/
theorem principal_kernel_criterion {ι : Type*} [Fintype ι] {d : ℕ}
    (Q : Matrix ι ι ℝ) (hsym : Q.IsSymm) (v : ι → ℝ) (hv : Q.mulVec v = 0)
    (e : Fin (d + 1) ≃ ι) (hlast : v (e (Fin.last d)) ≠ 0)
    (hprincipal : (Q.submatrix (fun i : Fin d => e i.castSucc)
      (fun i : Fin d => e i.castSucc)).PosDef) :
    Q.PosSemidef ∧ ∀ x : ι → ℝ,
      quadraticValue Q x = 0 ↔ ∃ t : ℝ, ∀ i, x i = t * v i := by
  have hsym' := hsym.submatrix e
  have hv' := mulVec_kernel_submatrix_equiv Q v hv e
  have hp : ((Q.submatrix e e).submatrix Fin.castSucc Fin.castSucc).PosDef := hprincipal
  have hpsd := posSemidef_of_principal_kernel (Q.submatrix e e) hsym'
    (v ∘ e) hv' hlast hp.posSemidef
  constructor
  · have h := hpsd.submatrix e.symm
    convert! h using 1
    ext i j
    simp
  · intro x
    have hquad : quadraticValue (Q.submatrix e e) (x ∘ e) = quadraticValue Q x := by
      rw [quadraticValue_submatrix_equiv]
      congr 1
      funext i
      simp
    rw [← hquad, quadraticValue_eq_zero_iff_span_kernel
      (Q.submatrix e e) hsym' (v ∘ e) hv' hlast hp]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, fun i => ?_⟩
      have hi := congrFun ht (e.symm i)
      simpa using hi
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      funext i
      exact ht (e i)

end DittertRybin.Certificates
