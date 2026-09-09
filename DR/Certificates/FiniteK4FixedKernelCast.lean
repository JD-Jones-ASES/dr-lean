import DR.Certificates.FiniteK4FixedBlocks

/-! Exact transport of the actual rational weighted-kernel identity. -/
namespace DittertRybin.Certificates
open scoped BigOperators

theorem finiteK4FixedFullMatrix_kernel_cast (coeff : Fin 407 → ℚ) (m n : ℕ) (s : Fin 10)
    (h : (finiteK4FixedFullMatrix coeff m n s).mulVec
      (finiteK4FixedWeight m n s : Fin (fourRowFiniteSeedFullSize s) → ℚ) = 0) :
    (finiteK4FixedFullMatrix (fun k => (coeff k : ℝ)) m n s).mulVec
      (finiteK4FixedWeight m n s : Fin (fourRowFiniteSeedFullSize s) → ℝ) = 0 := by
  rw [←finiteK4FixedFullMatrix_cast]
  ext i
  have he := congrArg (fun q : ℚ => (q : ℝ)) (congrFun h i)
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.zero_apply,
    Rat.cast_sum,Rat.cast_mul,Rat.cast_zero,finiteK4FixedWeight_cast] using he

end DittertRybin.Certificates
