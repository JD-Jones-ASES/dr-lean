import DR.Certificates.FiniteK3Ordinary
import DR.Certificates.PrincipalKernel

/-! The two small strict block checks give the full physical seed's exact
constant-vector kernel. Every matrix is built from the actual coefficient
roles; the aggregate kernel equation remains a finite check on that matrix. -/

namespace DittertRybin.Certificates
open scoped BigOperators

variable {ρ δ γ : Type*} [Fintype ρ] [Fintype δ] [Fintype γ]
  [DecidableEq ρ] [DecidableEq δ] [DecidableEq γ]

set_option maxHeartbeats 2000000 in
/-- A positive fluctuation block and a checked aggregate principal block imply
PSD and precisely the constant quadratic kernel for the actual physical seed. -/
theorem finiteK3Ordinary_kernel_criterion {d : ℕ} (coeff : Fin 93 → ℝ) (e f : ρ × δ)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (u : Fin (d+1) ≃ ((ρ × δ) ⊕ ρ))
    (hkernel : (finiteK3OrdinaryB coeff e f (Fintype.card γ)).mulVec
      (finiteK3AggregateKernel (Fintype.card γ)) = 0)
    (hB0 : ((finiteK3OrdinaryB coeff e f (Fintype.card γ)).submatrix
      (fun i : Fin d => u i.castSucc) (fun i : Fin d => u i.castSucc)).PosDef)
    (hH : (finiteK3OrdinaryH coeff e f).PosDef) :
    Matrix.PosSemidef (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2) :
      Matrix (ρ × (δ ⊕ γ)) (ρ × (δ ⊕ γ)) ℝ) ∧
    ∀ p : ρ × (δ ⊕ γ) → ℝ,
      quadraticValue (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)) p = 0 ↔
        ∃ t : ℝ, ∀ a, p a = t := by
  have hlast : finiteK3AggregateKernel (Fintype.card γ : ℝ) (u (Fin.last d)) ≠ 0 := by
    rcases h : u (Fin.last d) with a | a
    · simp [finiteK3AggregateKernel]
    · exact hell
  have hB := principal_kernel_criterion (finiteK3OrdinaryB coeff e f (Fintype.card γ))
    (finiteK3OrdinaryB_isSymm coeff e f _) (finiteK3AggregateKernel (Fintype.card γ))
    hkernel u hlast hB0
  have hBpsd := hB.1
  rw [finiteK3OrdinaryB_real] at hBpsd
  have hker (x : ρ × δ → ℝ) (z : ρ → ℝ) :
      quadraticValue (ordinaryAggregateMatrix (finiteK3OrdinaryA coeff e f)
        (finiteK3OrdinaryG coeff e f) (finiteK3OrdinaryD coeff e f)
        (finiteK3OrdinaryO coeff e f) (Fintype.card γ)) (Sum.elim x z) = 0 ↔
        ∃ t : ℝ, (∀ a, x a = t) ∧ ∀ a, z a = Fintype.card γ * t := by
    rw [← finiteK3OrdinaryB_real, hB.2]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, fun a => ?_, fun a => ?_⟩
      · simpa [finiteK3AggregateKernel] using ht (.inl a)
      · simpa [finiteK3AggregateKernel, mul_comm] using ht (.inr a)
    · rintro ⟨t, hx, hz⟩
      refine ⟨t, ?_⟩
      rintro (a | a)
      · simpa [finiteK3AggregateKernel] using hx a
      · simpa [finiteK3AggregateKernel, mul_comm] using hz a
  have hfull := ordinaryColumnMatrix_posSemidef
    (finiteK3OrdinaryA coeff e f) (finiteK3OrdinaryG coeff e f)
    (finiteK3OrdinaryD coeff e f) (finiteK3OrdinaryO coeff e f)
    (finiteK3OrdinaryA_isSymm coeff e f) (finiteK3OrdinaryD_isSymm coeff e f)
    (finiteK3OrdinaryO_isSymm coeff e f) hell hBpsd hH.posSemidef
  rw [← finiteK3Entry_ordinaryColumnMatrix] at hfull
  constructor
  · have h := hfull.submatrix (ordinaryCellEquiv (ρ := ρ) (δ := δ) (γ := γ)).symm
    have hid : (Matrix.submatrix
        (Matrix.submatrix (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2) :
          Matrix (ρ × (δ ⊕ γ)) (ρ × (δ ⊕ γ)) ℝ)
          ordinaryCellEquiv ordinaryCellEquiv)
        ordinaryCellEquiv.symm ordinaryCellEquiv.symm) =
        (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2) :
          Matrix (ρ × (δ ⊕ γ)) (ρ × (δ ⊕ γ)) ℝ) := by
      ext a b
      rcases a with ⟨r,c⟩
      rcases b with ⟨s,d⟩
      rcases c <;> rcases d <;> rfl
    rw [hid] at h
    exact h
  · intro p
    let x : ρ × δ → ℝ := fun a => p (a.1,Sum.inl a.2)
    let y : γ → ρ → ℝ := fun c a => p (a,Sum.inr c)
    have hquad :
        quadraticValue (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)) p =
        quadraticValue (ordinaryColumnMatrix (finiteK3OrdinaryA coeff e f)
          (finiteK3OrdinaryG coeff e f) (finiteK3OrdinaryD coeff e f)
          (finiteK3OrdinaryO coeff e f)) (Sum.elim x (fun q : γ × ρ => y q.1 q.2)) := by
      have hq := quadraticValue_submatrix_equiv
        (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2) :
          Matrix (ρ × (δ ⊕ γ)) (ρ × (δ ⊕ γ)) ℝ)
        (ordinaryCellEquiv (ρ := ρ) (δ := δ) (γ := γ))
        (Sum.elim x (fun q : γ × ρ => y q.1 q.2))
      rw [finiteK3Entry_ordinaryColumnMatrix] at hq
      have hv : (fun a : ρ × (δ ⊕ γ) =>
          Sum.elim x (fun q : γ × ρ => y q.1 q.2) (ordinaryCellEquiv.symm a)) = p := by
        funext a
        rcases a with ⟨r,c⟩
        rcases c <;> rfl
      rw [hv] at hq
      exact hq.symm
    rw [hquad, quadraticValue_ordinaryColumn_eq_zero_iff
      (finiteK3OrdinaryA coeff e f) (finiteK3OrdinaryG coeff e f)
      (finiteK3OrdinaryD coeff e f) (finiteK3OrdinaryO coeff e f) hell hBpsd hH hker]
    constructor
    · rintro ⟨t, hx, hy⟩
      refine ⟨t, ?_⟩
      rintro ⟨r, c | c⟩
      · exact hx (r,c)
      · exact hy c r
    · rintro ⟨t, ht⟩
      exact ⟨t, fun a => ht (a.1,Sum.inl a.2), fun c a => ht (a,Sum.inr c)⟩

end DittertRybin.Certificates
