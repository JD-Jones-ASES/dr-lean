import DR.Certificates.FiniteK4FixedCases.M5S0
import DR.Certificates.FiniteK4FixedCases.M5S1
import DR.Certificates.FiniteK4FixedCases.M5S2
import DR.Certificates.FiniteK4FixedCases.M5S3
import DR.Certificates.FiniteK4FixedCases.M5S4
import DR.Certificates.FiniteK4FixedCases.M5S5
import DR.Certificates.FiniteK4FixedCases.M5S6
import DR.Certificates.FiniteK4FixedCases.M5S7
import DR.Certificates.FiniteK4FixedCases.M5S8
import DR.Certificates.FiniteK4FixedCases.M5S9
import DR.Certificates.FiniteK4FixedKernelCast

/-! All ten exact block certificates for this fixed board. -/
namespace DittertRybin.Certificates
set_option Elab.async false

theorem finiteK4Fixed5_full_kernel (s : Fin 10) :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 s).mulVec
      (finiteK4FixedWeight 5 5 s : Fin (fourRowFiniteSeedFullSize s) → ℚ) = 0 := by
  fin_cases s
  · exact FiniteK4FixedCases.M5S0.full_kernel
  · exact FiniteK4FixedCases.M5S1.full_kernel
  · exact FiniteK4FixedCases.M5S2.full_kernel
  · exact FiniteK4FixedCases.M5S3.full_kernel
  · exact FiniteK4FixedCases.M5S4.full_kernel
  · exact FiniteK4FixedCases.M5S5.full_kernel
  · exact FiniteK4FixedCases.M5S6.full_kernel
  · exact FiniteK4FixedCases.M5S7.full_kernel
  · exact FiniteK4FixedCases.M5S8.full_kernel
  · exact FiniteK4FixedCases.M5S9.full_kernel

theorem finiteK4Fixed5_full_kernel_real (s : Fin 10) :
    (finiteK4FixedFullMatrix (fun k => (finiteK4Fixed5Coefficient k : ℝ)) 5 5 s).mulVec
      (finiteK4FixedWeight 5 5 s : Fin (fourRowFiniteSeedFullSize s) → ℝ) = 0 :=
  finiteK4FixedFullMatrix_kernel_cast _ _ _ _ (finiteK4Fixed5_full_kernel s)

theorem finiteK4Fixed5_principal_posDef (s : Fin 10) :
    (finiteK4FixedPrincipalMatrix (fun k => (finiteK4Fixed5Coefficient k : ℝ)) 5 5 s).PosDef := by
  rw [←finiteK4FixedPrincipalMatrix_cast]
  fin_cases s
  · exact FiniteK4FixedCases.M5S0.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S0.principal_valid
  · exact FiniteK4FixedCases.M5S1.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S1.principal_valid
  · exact FiniteK4FixedCases.M5S2.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S2.principal_valid
  · exact FiniteK4FixedCases.M5S3.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S3.principal_valid
  · exact FiniteK4FixedCases.M5S4.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S4.principal_valid
  · exact FiniteK4FixedCases.M5S5.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S5.principal_valid
  · exact FiniteK4FixedCases.M5S6.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S6.principal_valid
  · exact FiniteK4FixedCases.M5S7.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S7.principal_valid
  · exact FiniteK4FixedCases.M5S8.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S8.principal_valid
  · exact FiniteK4FixedCases.M5S9.principalGram.strictValid_posDef _ FiniteK4FixedCases.M5S9.principal_valid

theorem finiteK4Fixed5_row_posDef (s : Fin 10) :
    (finiteK4FixedRowMatrix (fun k => (finiteK4Fixed5Coefficient k : ℝ)) 5 s).PosDef := by
  rw [←finiteK4FixedRowMatrix_cast]
  fin_cases s
  · exact FiniteK4FixedCases.M5S0.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S0.row_valid
  · exact FiniteK4FixedCases.M5S1.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S1.row_valid
  · exact FiniteK4FixedCases.M5S2.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S2.row_valid
  · exact FiniteK4FixedCases.M5S3.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S3.row_valid
  · exact FiniteK4FixedCases.M5S4.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S4.row_valid
  · exact FiniteK4FixedCases.M5S5.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S5.row_valid
  · exact FiniteK4FixedCases.M5S6.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S6.row_valid
  · exact FiniteK4FixedCases.M5S7.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S7.row_valid
  · exact FiniteK4FixedCases.M5S8.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S8.row_valid
  · exact FiniteK4FixedCases.M5S9.rowGram.strictValid_posDef _ FiniteK4FixedCases.M5S9.row_valid

theorem finiteK4Fixed5_column_posDef (s : Fin 10) :
    (finiteK4FixedColumnMatrix (fun k => (finiteK4Fixed5Coefficient k : ℝ)) 5 s).PosDef := by
  rw [←finiteK4FixedColumnMatrix_cast]
  fin_cases s
  · exact FiniteK4FixedCases.M5S0.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S0.column_valid
  · exact FiniteK4FixedCases.M5S1.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S1.column_valid
  · exact FiniteK4FixedCases.M5S2.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S2.column_valid
  · exact FiniteK4FixedCases.M5S3.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S3.column_valid
  · exact FiniteK4FixedCases.M5S4.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S4.column_valid
  · exact FiniteK4FixedCases.M5S5.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S5.column_valid
  · exact FiniteK4FixedCases.M5S6.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S6.column_valid
  · exact FiniteK4FixedCases.M5S7.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S7.column_valid
  · exact FiniteK4FixedCases.M5S8.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S8.column_valid
  · exact FiniteK4FixedCases.M5S9.columnGram.strictValid_posDef _ FiniteK4FixedCases.M5S9.column_valid

theorem finiteK4Fixed5_interaction_posDef (s : Fin 10) :
    (finiteK4FixedInteractionMatrix (fun k => (finiteK4Fixed5Coefficient k : ℝ)) s).PosDef := by
  rw [←finiteK4FixedInteractionMatrix_cast]
  fin_cases s
  · exact FiniteK4FixedCases.M5S0.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S0.interaction_valid
  · exact FiniteK4FixedCases.M5S1.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S1.interaction_valid
  · exact FiniteK4FixedCases.M5S2.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S2.interaction_valid
  · exact FiniteK4FixedCases.M5S3.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S3.interaction_valid
  · exact FiniteK4FixedCases.M5S4.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S4.interaction_valid
  · exact FiniteK4FixedCases.M5S5.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S5.interaction_valid
  · exact FiniteK4FixedCases.M5S6.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S6.interaction_valid
  · exact FiniteK4FixedCases.M5S7.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S7.interaction_valid
  · exact FiniteK4FixedCases.M5S8.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S8.interaction_valid
  · exact FiniteK4FixedCases.M5S9.interactionGram.strictValid_posDef _ FiniteK4FixedCases.M5S9.interaction_valid

end DittertRybin.Certificates
