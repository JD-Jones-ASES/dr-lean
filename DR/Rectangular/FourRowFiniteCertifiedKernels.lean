import DR.Rectangular.FourRowFiniteSeedKernelEvaluation
import DR.Rectangular.FourRowFiniteData5FullKernel
import DR.Rectangular.FourRowFiniteData50FullKernel
import DR.Rectangular.FourRowFiniteCertifiedBlocks

/-! Actual full compressed weighted kernels for both checked parameter families. -/

namespace DittertRybin
noncomputable section

theorem fourRowFinite5_full_kernel (s : Fin 10) (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :
    (fourRowFiniteSeedFullMatrix s (5/u) (fourRowFinite5RoleValue u)).mulVec
      (fun j => fourRowFiniteSeedWeight s (5/u) j.val) = 0 := by
  exact fourRowFiniteSeedFullMatrix_kernel_of_coefficients fourRowFiniteFamilyNumerator5
    (by decide) (by linarith : 0 < u) hu.2 s (fourRowFinite5_full_kernel_coefficients s)

theorem fourRowFinite50_full_kernel (s : Fin 10) (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :
    (fourRowFiniteSeedFullMatrix s (50/u) (fourRowFinite50RoleValue u)).mulVec
      (fun j => fourRowFiniteSeedWeight s (50/u) j.val) = 0 := by
  exact fourRowFiniteSeedFullMatrix_kernel_of_coefficients fourRowFiniteFamilyNumerator50
    (by decide) (by linarith : 0 < u) hu.2 s (fourRowFinite50_full_kernel_coefficients s)

theorem fourRowFiniteSeedWeight_parameter_pos (s : Fin 10) {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (j : ℕ) :
    0 < fourRowFiniteSeedWeight s ((a : ℝ)/u) j := by
  apply fourRowFiniteSeedWeight_pos
  apply (lt_div_iff₀ hu).mpr
  have ha' : (5 : ℝ) ≤ a := by exact_mod_cast ha
  linarith

end
end DittertRybin
