import DR.Certificates.Gram
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.Star.Real

/-!
Boundary and negative controls for the exact Gram soundness layer.
`decide +kernel` checks finite rational propositions by kernel reduction;
no native decision procedure or external verifier is trusted.
-/

namespace DittertRybin.Tests.Gram

open DittertRybin.Certificates
open scoped BigOperators

private def lap : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; -1, 1]
private def cg : GramCertificate 2 1 :=
  ⟨fun _ => 1, fun _ i => if i = 0 then 1 else -1⟩

example : cg.Valid lap := by decide +kernel

example : (lap.map (fun q : ℚ => (q : ℝ))).PosSemidef :=
  cg.posSemidef lap (by decide +kernel)

-- Keeping positive weights while corrupting one matrix entry must fail the identity gate.
example : ¬ cg.Valid (!![2, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by decide +kernel

-- Negating both the weight and Gram matrix preserves factorization but fails positivity.
example : ¬ (⟨fun _ => -1, cg.factor⟩ : GramCertificate 2 1).Valid (-lap) := by decide +kernel

private def cz : GramCertificate 2 2 :=
  ⟨![1, 0], fun i j => if i = j then 1 else 0⟩

-- Zero pivots are valid PSD certificates and may leave a nonzero quadratic-kernel vector.
example : cz.Valid (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) := by decide +kernel

example : quadraticValue
    ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ).map (fun q : ℚ => (q : ℝ))) ![0, 1] = 0 := by
  norm_num [quadraticValue, Fin.sum_univ_two]

example : (⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩ : GramCertificate 0 0).Valid 0 := by
  decide +kernel

-- A nontrivial triangular LDL identity gives strict positivity on the whole real space.
example : ((!![4, 2; 2, 2] : Matrix (Fin 2) (Fin 2) ℚ).map (fun q : ℚ => (q : ℝ))).PosDef := by
  apply GramCertificate.ofLDL_posDef (!![1, 0; 1 / 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) ![4, 1]
  · norm_num [Fin.forall_fin_succ]
  · norm_num [Fin.forall_fin_succ, Fin.sum_univ_two]
  · norm_num [Fin.forall_fin_succ]
  · norm_num [Fin.forall_fin_succ]

example (x : Fin 0 → ℝ) : quadraticValue ((centeringMatrix 0).map (fun q : ℚ => (q : ℝ))) x = 0 := by
  simp [quadraticValue]

-- A one-dimensional principal certificate lifts through the independently checked kernel.
example : (lap.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply rational_principal_gram_posSemidef lap (by norm_num [lap, Fin.forall_fin_succ])
    (fun _ => 1) (by norm_num [lap, Fin.forall_fin_succ, Fin.sum_univ_succ]) (by norm_num)
    (⟨fun _ => 1, fun _ _ => 1⟩ : GramCertificate 1 1)
  decide +kernel

-- The exact kernel is the constant line, including the zero vector.
example (x : Fin 2 → ℝ) :
    quadraticValue (lap.map (fun q : ℚ => (q : ℝ))) x = 0 ↔ x 0 = x 1 := by
  let Q := lap.map (fun q : ℚ => (q : ℝ))
  have hsym : Q.IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Q, lap]
  have hker : Q.mulVec (fun _ => 1) = 0 := by
    ext i
    fin_cases i <;> norm_num [Q, lap, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hprincipal : (Q.submatrix Fin.castSucc Fin.castSucc).PosDef := by
    have heq : Q.submatrix Fin.castSucc Fin.castSucc = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      fin_cases i
      fin_cases j
      norm_num [Q, lap]
    rw [heq]
    exact Matrix.PosDef.one
  rw [quadraticValue_eq_zero_iff_span_kernel Q hsym (fun _ => 1) hker (by norm_num) hprincipal]
  constructor
  · rintro ⟨c, rfl⟩
    rfl
  · intro h
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i
    · simp
    · simpa using h.symm

-- A positive principal block without the kernel equation can hide a negative direction.
example : ¬ (Matrix.of (fun i j : Fin 2 =>
    if i = j then if i = 0 then (1 : ℝ) else -1 else 0)).PosSemidef := by
  intro h
  have hv := h.dotProduct_mulVec_nonneg ![0, 1]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv

-- The shifted certificate gives the exact variance lower bound in a singular example.
example (x : Fin 2 → ℝ) :
    2 * ((∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / 2) ≤
      quadraticValue (lap.map (fun q : ℚ => (q : ℝ))) x := by
  apply quadraticValue_lower_of_centered_shift lap 2
  have heq : lap - (2 : ℚ) • centeringMatrix 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [lap, centeringMatrix]
  simpa [heq] using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef)

#print axioms GramCertificate.posSemidef
#print axioms GramCertificate.ofLDL_posDef
#print axioms rational_principal_gram_posSemidef
#print axioms quadraticValue_eq_zero_iff_span_kernel
#print axioms quadraticValue_lower_of_centered_shift

end DittertRybin.Tests.Gram
