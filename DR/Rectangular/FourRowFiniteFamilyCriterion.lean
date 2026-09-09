import DR.Rectangular.FourRowFiniteCertifiedKernels
import DR.Rectangular.FourRowFiniteFamilySoundness
import DR.Certificates.FiniteK4QuinticRows

/-! Both actual coefficient families have PSD matrices and exact constant
kernels for every multiplier triple throughout their closed parameter interval. -/

namespace DittertRybin
open Certificates
noncomputable section

theorem fourRowFinite5_entry_criterion {N : ℕ} (hN : 5 ≤ N) (u : ℝ)
    (hu : 1/10 ≤ u ∧ u ≤ 1) (hNu : (N : ℝ) = 5/u) (t : Fin 3 → Fin 4 × Fin N) :
    (finiteK4Entry (fourRowFiniteUniversalCoefficient fourRowFiniteFamilyNumerator5 u) t).PosSemidef ∧
      ∀ x : Fin 4 × Fin N → ℝ,
        quadraticValue (finiteK4Entry
          (fourRowFiniteUniversalCoefficient fourRowFiniteFamilyNumerator5 u) t) x = 0 ↔
            ∃ c : ℝ, ∀ i, x i = c := by
  apply fourRowFinite_family_entry_criterion hN (fourRowFinite5RoleValue u) u (by linarith) _ _ _ _ _ t
  · intro s; rw [hNu]; exact fourRowFinite5_full_kernel s u hu
  · intro s; rw [hNu]; exact fourRowFinite5_trivial_posDef s u hu
  · intro s hr; rw [hNu]; exact fourRowFinite5_row_posDef s u hu hr
  · intro s; exact fourRowFinite5_column_posDef s u hu
  · intro s hr; exact fourRowFinite5_interaction_posDef s u hu hr

theorem fourRowFinite50_entry_criterion {N : ℕ} (hN : 5 ≤ N) (u : ℝ)
    (hu : 1/10 ≤ u ∧ u ≤ 1) (hNu : (N : ℝ) = 50/u) (t : Fin 3 → Fin 4 × Fin N) :
    (finiteK4Entry (fourRowFiniteUniversalCoefficient fourRowFiniteFamilyNumerator50 u) t).PosSemidef ∧
      ∀ x : Fin 4 × Fin N → ℝ,
        quadraticValue (finiteK4Entry
          (fourRowFiniteUniversalCoefficient fourRowFiniteFamilyNumerator50 u) t) x = 0 ↔
            ∃ c : ℝ, ∀ i, x i = c := by
  apply fourRowFinite_family_entry_criterion hN (fourRowFinite50RoleValue u) u (by linarith) _ _ _ _ _ t
  · intro s; rw [hNu]; exact fourRowFinite50_full_kernel s u hu
  · intro s; rw [hNu]; exact fourRowFinite50_trivial_posDef s u hu
  · intro s hr; rw [hNu]; exact fourRowFinite50_row_posDef s u hu hr
  · intro s; exact fourRowFinite50_column_posDef s u hu
  · intro s hr; exact fourRowFinite50_interaction_posDef s u hu hr

end
end DittertRybin
