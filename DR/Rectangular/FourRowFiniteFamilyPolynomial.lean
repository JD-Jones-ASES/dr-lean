import DR.Rectangular.FourRowFiniteDataLookup
import DR.Rectangular.FourRowFinitePolynomialBlocks
import DR.Rectangular.FourRowFiniteLinearEvaluation
import DR.Certificates.FiniteK4Orbits
import DR.Certificates.BernsteinTransform
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Role-indexed family polynomials

The literal numerator table is attached to actual role keys through a fully
checked inverse of the complete four-row catalogue. No assertion is made
about a lookup input outside that catalogue.
-/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial Certificates
noncomputable section

def fourRowFiniteFamilyRolePolynomial (h : Fin 391 → Fin 5 → ℚ)
    (key : ℕ) : FourRowFiniteUnivariate :=
  powerPolynomial (h (fourRowFiniteRoleLookup key))

theorem fourRowFiniteFamilyRolePolynomial_key (h : Fin 391 → Fin 5 → ℚ) (k : Fin 391) :
    fourRowFiniteFamilyRolePolynomial h
      (finiteK4RoleKeys.get (finiteK4FourRowRoleIndices.get k)) = powerPolynomial (h k) := by
  simp only [fourRowFiniteFamilyRolePolynomial, fourRowFiniteRoleLookup_key]

theorem fourRowFiniteFamilyRolePolynomial_eval (h : Fin 391 → Fin 5 → ℚ)
    (key : ℕ) (u : ℝ) :
    rationalEval (fun _ => u) (fourRowFiniteFamilyRolePolynomial h key) =
      fourRowFiniteNumeratorValue h (fourRowFiniteRoleLookup key) u := by
  simp only [fourRowFiniteFamilyRolePolynomial, powerPolynomial, rationalEval,
    eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Rat.coe_castHom,
    fourRowFiniteNumeratorValue]

theorem fourRowFiniteFamilyRolePolynomial_totalDegree (h : Fin 391 → Fin 5 → ℚ)
    (key : ℕ) : (fourRowFiniteFamilyRolePolynomial h key).totalDegree ≤ 4 := by
  unfold fourRowFiniteFamilyRolePolynomial powerPolynomial
  apply totalDegree_finsetSum_le
  intro k _
  exact (totalDegree_mul _ _).trans (by
    simp only [totalDegree_C, totalDegree_X_pow, zero_add]
    omega)

/-- The lookup selects the actual catalogue role on every tuple with a repeated row. -/
theorem fourRowFiniteRoleLookup_tuple (s : Fin 5 → ℕ × ℕ)
    (hr : ¬Function.Injective (fun i => (s i).1)) :
    finiteK4FourRowRoleIndices.get (fourRowFiniteRoleLookup (finiteK4TupleRoleKey s)) =
      finiteK4RoleIndex s := by
  obtain ⟨k, hk⟩ := finiteK4RoleIndex_fourRows s hr
  rw [finiteK4RoleIndex_spec, ← hk, fourRowFiniteRoleLookup_key]

/-- In particular the lookup is exact for every physical four-row board, including empty ones. -/
theorem fourRowFiniteRoleLookup_finFour {n : ℕ} (s : Fin 5 → Fin 4 × Fin n) :
    finiteK4FourRowRoleIndices.get (fourRowFiniteRoleLookup
      (finiteK4TupleRoleKey (fun i => ((s i).1.val, (s i).2.val)))) =
      finiteK4RoleIndex (fun i => ((s i).1.val, (s i).2.val)) := by
  obtain ⟨k, hk⟩ := finiteK4RoleIndex_finFour s
  rw [finiteK4RoleIndex_spec, ← hk, fourRowFiniteRoleLookup_key]

end
end DittertRybin
