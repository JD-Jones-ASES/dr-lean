import DR.Rectangular.FourRowFiniteLinear

namespace DittertRybin
open scoped BigOperators
noncomputable section

def fourRowFiniteNumeratorValue (h : Fin 391 → Fin 5 → ℚ) (i : Fin 391) (u : ℝ) : ℝ :=
  ∑ d, (h i d : ℝ)*u^(d : ℕ)

private theorem fourRowFiniteNumeratorValue_sum (terms : List (Fin 391 × ℕ))
    (h : Fin 391 → Fin 5 → ℚ) (u : ℝ) :
    (terms.map (fun t => (t.2 : ℝ)*fourRowFiniteNumeratorValue h t.1 u)).sum =
      ∑ d : Fin 5, ((terms.map (fun t => (t.2 : ℚ)*h t.1 d)).sum : ℝ)*u^(d : ℕ) := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      add_mul, Finset.sum_add_distrib]
    rw [ih]
    congr 1
    simp only [fourRowFiniteNumeratorValue, Finset.mul_sum, mul_assoc]

/-- The finite coefficient gate yields the actual polynomial value for every real parameter. -/
theorem FourRowFiniteCoefficientRow.Valid.eval (row : FourRowFiniteCoefficientRow)
    (a : ℕ) (h : Fin 391 → Fin 5 → ℚ) (hv : row.Valid a h) (u : ℝ) :
    (row.terms.map (fun t => (t.2 : ℝ)*fourRowFiniteNumeratorValue h t.1 u)).sum =
      u*((row.multiplicity : ℝ)*
        (1-87/(16*a)*u+319/(32*a^2)*u^2-87/(16*a^3)*u^3)-row.successes) := by
  rw [fourRowFiniteNumeratorValue_sum]
  unfold FourRowFiniteCoefficientRow.Valid at hv
  simp only [hv]
  simp [fourRowFiniteCoefficientRhs, Fin.sum_univ_succ]
  ring

private def fourRowFiniteKernelCoefficient (a : ℕ) (h : Fin 391 → Fin 5 → ℚ)
    (t : FourRowFiniteKernelTerm) (d : Fin 6) : ℚ :=
  (a : ℚ)*t.slope*fourRowFiniteNumeratorExtend h t.role d +
    if (d : ℕ) = 0 then 0 else (t.offset : ℚ)*fourRowFiniteNumeratorExtend h t.role (d-1)

private theorem fourRowFiniteKernelCoefficient_eval (a : ℕ) (h : Fin 391 → Fin 5 → ℚ)
    (t : FourRowFiniteKernelTerm) (u : ℝ) :
    ((a : ℝ)*t.slope+(t.offset : ℝ)*u)*fourRowFiniteNumeratorValue h t.role u =
      ∑ d : Fin 6, (fourRowFiniteKernelCoefficient a h t d : ℝ)*u^(d : ℕ) := by
  simp [fourRowFiniteKernelCoefficient, fourRowFiniteNumeratorExtend,
    fourRowFiniteNumeratorValue, Fin.sum_univ_succ]
  ring

/-- All six checked coefficients give the polynomial row-kernel identity. -/
theorem fourRowFiniteKernelValid.eval (row : List FourRowFiniteKernelTerm)
    (a : ℕ) (h : Fin 391 → Fin 5 → ℚ) (hv : fourRowFiniteKernelValid row a h) (u : ℝ) :
    (row.map (fun t => ((a : ℝ)*t.slope+(t.offset : ℝ)*u)*
      fourRowFiniteNumeratorValue h t.role u)).sum = 0 := by
  have he : (row.map (fun t => ((a : ℝ)*t.slope+(t.offset : ℝ)*u)*
        fourRowFiniteNumeratorValue h t.role u)).sum =
      ∑ d : Fin 6, ((row.map (fun t => fourRowFiniteKernelCoefficient a h t d)).sum : ℝ)*u^(d : ℕ) := by
    clear hv
    induction row with
    | nil => simp
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, Rat.cast_add]
      rw [ih, fourRowFiniteKernelCoefficient_eval]
      simp only [add_mul, Finset.sum_add_distrib]
  rw [he]
  unfold fourRowFiniteKernelValid at hv
  simp only [fourRowFiniteKernelCoefficient, hv, Rat.cast_zero, zero_mul, Finset.sum_const_zero]

/-- Dividing by `u²` gives the actual affine-count kernel for coefficients `h(u)/u`. -/
theorem fourRowFiniteKernelValid.eval_div (row : List FourRowFiniteKernelTerm)
    (a : ℕ) (h : Fin 391 → Fin 5 → ℚ) (hv : fourRowFiniteKernelValid row a h)
    (u : ℝ) (hu : u ≠ 0) :
    (row.map (fun t => (((a : ℝ)/u)*t.slope+t.offset)*
      (fourRowFiniteNumeratorValue h t.role u/u))).sum = 0 := by
  have he : (row.map (fun t => (((a : ℝ)/u)*t.slope+t.offset)*
        (fourRowFiniteNumeratorValue h t.role u/u))).sum =
      (row.map (fun t => ((a : ℝ)*t.slope+(t.offset : ℝ)*u)*
        fourRowFiniteNumeratorValue h t.role u)).sum/u^2 := by
    clear hv
    induction row with
    | nil => simp
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, add_div]
      rw [ih]
      congr 1
      field_simp
  rw [he, hv.eval, zero_div]

end
end DittertRybin
