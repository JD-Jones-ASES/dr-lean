import DR.Rectangular.FourRowFinitePhysicalMatrix
import DR.Rectangular.FourRowFinitePairSoundness

/-! Exact PSD and constant-kernel transport to the actual finite-role matrix. -/

namespace DittertRybin
open scoped BigOperators
open Certificates
noncomputable section

theorem fourRowFiniteSeedMatrix_criterion {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (s : Fin 10) (h : ℕ → ℝ)
    (hQ : (twoAxisOrdinaryMatrix (ρ := Fin (m-fourRowFiniteSeedRows s))
      (γ := Fin (n-fourRowFiniteSeedColumns s)) (fourRowFiniteSeedRelationKernel s h)).PosSemidef)
    (hker : ∀ x : (Fin (fourRowFiniteSeedRows s) ⊕ Fin (m-fourRowFiniteSeedRows s)) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Fin (n-fourRowFiniteSeedColumns s)) → ℝ,
      quadraticValue (twoAxisOrdinaryMatrix (fourRowFiniteSeedRelationKernel s h)) x = 0 ↔
        ∃ t : ℝ, ∀ i, x i = t) :
    (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)) (finiteTriplePhysicalSeed hm hn s)).PosSemidef ∧
      ∀ x : Fin m × Fin n → ℝ,
        quadraticValue (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k))
          (finiteTriplePhysicalSeed hm hn s)) x = 0 ↔ ∃ t : ℝ, ∀ i, x i = t := by
  have he := fourRowFiniteSeedMatrix_physical hm hn s h
  have hback : (twoAxisOrdinaryMatrix (fourRowFiniteSeedRelationKernel s h)).submatrix
      (fourRowFiniteSeedPhysicalEquiv hm hn s).symm (fourRowFiniteSeedPhysicalEquiv hm hn s).symm =
      finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)) (finiteTriplePhysicalSeed hm hn s) := by
    rw [← he]
    ext i j
    simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
  rw [← hback]
  exact psd_constant_kernel_submatrix _ (fourRowFiniteSeedPhysicalEquiv hm hn s).symm hQ hker

theorem fourRowFiniteSeedPhysical_criterion_of_blocks {N : ℕ} (hN : 5 ≤ N)
    (s : Fin 10) (h : ℕ → ℝ)
    (hk : (fourRowFiniteSeedFullMatrix s N h).mulVec
      (fun j => fourRowFiniteSeedWeight s N j.val) = 0)
    (hp : (fourRowFiniteSeedTrivialMatrix s N h).PosDef)
    (hrow : fourRowFiniteSeedRows s < 3 → (fourRowFiniteSeedRowMatrix s N h).PosDef)
    (hcol : (fourRowFiniteSeedColumnMatrix s h).PosDef)
    (hinter : fourRowFiniteSeedRows s < 3 → (fourRowFiniteSeedInteractionMatrix s h).PosDef) :
    (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k))
      (finiteTriplePhysicalSeed (by decide : 3 ≤ 4) (by omega : 3 ≤ N) s)).PosSemidef ∧
      ∀ x : Fin 4 × Fin N → ℝ,
        quadraticValue (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k))
          (finiteTriplePhysicalSeed (by decide : 3 ≤ 4) (by omega : 3 ≤ N) s)) x = 0 ↔
            ∃ t : ℝ, ∀ i, x i = t := by
  obtain ⟨hQ,hker⟩ := fourRowFiniteSeedRelation_criterion hN s h hk hp hrow hcol hinter
  exact fourRowFiniteSeedMatrix_criterion (by decide) (by omega) s h hQ hker

theorem fourRowFinite_psd_constant_kernel_smul {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef)
    (hker : ∀ x : ι → ℝ, quadraticValue Q x = 0 ↔ ∃ t : ℝ, ∀ i, x i = t)
    (d : ℝ) (hd : 0 < d) :
    (d • Q).PosSemidef ∧ ∀ x : ι → ℝ,
      quadraticValue (d • Q) x = 0 ↔ ∃ t : ℝ, ∀ i, x i = t := by
  refine ⟨hQ.smul hd.le,fun x => ?_⟩
  have he : quadraticValue (d • Q) x = d*quadraticValue Q x := by
    simp only [quadraticValue,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,
      mul_comm,mul_left_comm]
  rw [he,mul_eq_zero]
  simp only [hd.ne',false_or,hker]

theorem fourRowFiniteEntry_smul {m n : ℕ} (h : ℕ → ℝ) (d : ℝ)
    (t : Fin 3 → Fin m × Fin n) :
    finiteK4Entry (fun k => d*h (finiteK4RoleKeys.get k)) t =
      d • finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)) t := rfl

end
end DittertRybin
