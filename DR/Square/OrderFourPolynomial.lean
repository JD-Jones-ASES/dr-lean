import DR.EndpointIdentity
import DR.Certificates.Bernstein
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The actual order-four probability polynomial

The sixteen variables use row-major cell order. The quartic is exactly
the inclusive-OR probability polynomial for four ordered iid samples,
using the already-proved endpoint counting identity. All identities in
this module hold over arbitrary real cell weights before normalization.
-/

open scoped BigOperators

namespace DittertRybin

def orderFourCell : (Fin 4 × Fin 4) ≃ Fin 16 := finProdFinEquiv

theorem orderFourCell_val (i j : Fin 4) : (orderFourCell (i,j)).val = 4*i.val+j.val := by
  simp [orderFourCell, finProdFinEquiv]
  omega

def orderFourFlat (A : Board 4 4) : Fin 16 → ℝ :=
  fun u => A (orderFourCell.symm u).1 (orderFourCell.symm u).2

def orderFourUnflat (p : Fin 16 → ℝ) : Board 4 4 :=
  fun i j => p (orderFourCell (i,j))

theorem orderFourUnflat_flat (A : Board 4 4) : orderFourUnflat (orderFourFlat A) = A := by
  ext i j
  simp [orderFourUnflat, orderFourFlat]

theorem orderFourFlat_unflat (p : Fin 16 → ℝ) : orderFourFlat (orderFourUnflat p) = p := by
  ext u
  simp [orderFourUnflat, orderFourFlat]

theorem orderFour_sum_flat (A : Board 4 4) : (∑ u, orderFourFlat A u) = totalMass A := by
  rw [← Equiv.sum_comp orderFourCell]
  simp [orderFourFlat, Fintype.sum_prod_type, totalMass, rowSum]

noncomputable def orderFourTotalPolynomial : MvPolynomial (Fin 16) ℚ :=
  ∑ u, MvPolynomial.X u

noncomputable def orderFourQuarticPolynomial : MvPolynomial (Fin 16) ℚ :=
  MvPolynomial.C 24 *
    ((∏ i : Fin 4, ∑ j : Fin 4, MvPolynomial.X (orderFourCell (i,j))) +
      (∏ j : Fin 4, ∑ i : Fin 4, MvPolynomial.X (orderFourCell (i,j))) -
      Matrix.permanent (fun i j : Fin 4 => MvPolynomial.X (orderFourCell (i,j))))

noncomputable def orderFourSexticGapPolynomial : MvPolynomial (Fin 16) ℚ :=
  MvPolynomial.C (183/1024) * orderFourTotalPolynomial^6 -
    orderFourTotalPolynomial^2 * orderFourQuarticPolynomial

theorem orderFourTotalPolynomial_eval (p : Fin 16 → ℝ) :
    Certificates.rationalEval p orderFourTotalPolynomial = ∑ u, p u := by
  simp [Certificates.rationalEval, orderFourTotalPolynomial]

/-- The quartic is the actual iid-cell separation polynomial, including
the factorial for ordered samples and the inclusive-OR intersection subtraction. -/
theorem orderFourQuarticPolynomial_eval (p : Fin 16 → ℝ) :
    Certificates.rationalEval p orderFourQuarticPolynomial =
      separationProbability (orderFourUnflat p) 4 := by
  rw [separationProbability_endpoint]
  norm_num [Certificates.rationalEval, orderFourQuarticPolynomial, orderFourUnflat,
    rowSum, colSum, Matrix.permanent, Nat.factorial]

theorem orderFourSexticGapPolynomial_eval (p : Fin 16 → ℝ) :
    Certificates.rationalEval p orderFourSexticGapPolynomial =
      (183/1024:ℝ)*(∑ u, p u)^6 - (∑ u, p u)^2 *
        separationProbability (orderFourUnflat p) 4 := by
  simp only [orderFourSexticGapPolynomial, Certificates.rationalEval,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow]
  norm_num only [map_div₀, map_natCast]
  change (183/1024:ℝ) * Certificates.rationalEval p orderFourTotalPolynomial ^ 6 -
    Certificates.rationalEval p orderFourTotalPolynomial ^ 2 *
      Certificates.rationalEval p orderFourQuarticPolynomial = _
  rw [orderFourTotalPolynomial_eval, orderFourQuarticPolynomial_eval]

theorem orderFourSexticGapPolynomial_probability (A : Board 4 4) (hA : IsProbability A) :
    Certificates.rationalEval (orderFourFlat A) orderFourSexticGapPolynomial =
      (183/1024:ℝ) - separationProbability A 4 := by
  rw [orderFourSexticGapPolynomial_eval, orderFour_sum_flat, hA.2, orderFourUnflat_flat]
  ring

theorem orderFour_uniform_value : separationProbability (uniformBoard 4 4) 4 = (183/1024:ℝ) := by
  rw [separationProbability_uniform (by decide) (by decide)]
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

theorem orderFourTotalPolynomial_isHomogeneous : orderFourTotalPolynomial.IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum Finset.univ _ 1 (fun i _ => MvPolynomial.isHomogeneous_X ℚ i)

theorem orderFourQuarticPolynomial_isHomogeneous : orderFourQuarticPolynomial.IsHomogeneous 4 := by
  have hp (f : Fin 4 → Fin 16) :
      (∏ i, (MvPolynomial.X (f i) : MvPolynomial (Fin 16) ℚ)).IsHomogeneous 4 := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X ℚ (f i))
  have hrows : (∏ i : Fin 4, ∑ j : Fin 4,
      (MvPolynomial.X (orderFourCell (i,j)) : MvPolynomial (Fin 16) ℚ)).IsHomogeneous 4 := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 1)
      (fun i _ => MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
        (fun j _ => MvPolynomial.isHomogeneous_X ℚ (orderFourCell (i,j))))
  have hcols : (∏ j : Fin 4, ∑ i : Fin 4,
      (MvPolynomial.X (orderFourCell (i,j)) : MvPolynomial (Fin 16) ℚ)).IsHomogeneous 4 := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 1)
      (fun j _ => MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
        (fun i _ => MvPolynomial.isHomogeneous_X ℚ (orderFourCell (i,j))))
  have hperm : (Matrix.permanent (fun i j : Fin 4 =>
      (MvPolynomial.X (orderFourCell (i,j)) : MvPolynomial (Fin 16) ℚ))).IsHomogeneous 4 :=
    MvPolynomial.IsHomogeneous.sum Finset.univ _ 4
      (fun σ _ => hp (fun i => orderFourCell (σ i,i)))
  exact ((hrows.add hcols).sub hperm).C_mul 24

theorem orderFourSexticGapPolynomial_isHomogeneous : orderFourSexticGapPolynomial.IsHomogeneous 6 := by
  have h6 : (orderFourTotalPolynomial^6).IsHomogeneous 6 := by
    simpa using orderFourTotalPolynomial_isHomogeneous.pow 6
  have h2 : (orderFourTotalPolynomial^2).IsHomogeneous 2 := by
    simpa using orderFourTotalPolynomial_isHomogeneous.pow 2
  exact (h6.C_mul (183/1024)).sub (h2.mul orderFourQuarticPolynomial_isHomogeneous)

end DittertRybin
