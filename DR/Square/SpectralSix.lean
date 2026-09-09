import DR.Square.SixMatrixBounds
import DR.Square.SixSweepCut
import DR.Certificates.SpectralSix
import DR.Square.Maximizers

/-!
# The actual order-six square contradiction

The two scalar certificates apply to the same actual balanced cut. The
singleton case retains its distinguished matrix entry in the permanent;
the other two cardinalities use both near-stochastic diagonal blocks.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralSixGuards Certificates.SpectralSix

/-- Either of the two actual permanent floors contradicts its exact scalar
certificate. No boundary entry is assumed positive. -/
theorem six_balanced_cut_contradiction (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A)
    (I J : Finset (Fin 6)) (hcard : I.card = J.card) (hlo : 1 ≤ I.card) (hhi : I.card ≤ 3)
    (hcross : cutMass A I Jᶜ + cutMass A Iᶜ J ≤
      crossingBound (sixDeficitParameter (dittertConstant 6 - A.permanent)))
    (hext : I.card = 1 → ∀ i ∈ I, ∀ j ∈ J,
      ((∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j)) ∨
      ((∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c))) : False := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  let t := sixDeficitParameter (dittertConstant 6 - A.permanent)
  let q := sixDominationFactor t
  let w := crossingBound t
  have ht : 0 ≤ t := sixDeficitParameter_nonneg _
  have ht1 : t ≤ 31 / 100 := (sixDeficitParameter_le_cap hd0 hdg).le
  have hq : 0 < q := by have := sixDominationFactor_gt_two_thirds ht ht1; dsimp [q]; linarith
  have hw : w < 2 * q := by
    have hqw := sixDominationFactor_gt_two_thirds ht ht1
    have hww := crossingBound_lt_one_sixth t ht ht1
    dsimp [w, q]
    linarith
  have hbase : 0 ≤ q - w / 2 := (permanent_base_pos t ht ht1).le
  obtain ⟨B, hB, hdom⟩ := six_contender_dominated_doublyStochastic A hA hmass hcont
  change ∀ i j, q * B i j ≤ A i j at hdom
  change cutMass A I Jᶜ + cutMass A Iᶜ J ≤ w at hcross
  by_cases hsingle : I.card = 1
  · have hJsingle : J.card = 1 := hcard ▸ hsingle
    obtain ⟨i, hI⟩ := Finset.card_eq_one.mp hsingle
    obtain ⟨j, hJ⟩ := Finset.card_eq_one.mp hJsingle
    have horient := hext hsingle i (by simp [hI]) j (by simp [hJ])
    rw [hI, hJ] at hcross
    have hcell := six_globalMax_singleton_cell_lower A hA hmass hmax i j w horient hcross
    have hfloor := permanent_lower_bound_singleton_six A B hA hB q hq hdom i j w hcross hw
    have hcellfloor := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcell (dittertConstant_pos (by norm_num : 0 < 5)).le)
      (pow_nonneg hbase 5)
    have hstrict := singleton_floor_gt_deficit hd0 hdg
    change dittertConstant 6 - (dittertConstant 6 - A.permanent) <
      (1 - w / 2 - (cellCorrection : ℝ)) * dittertConstant 5 * (q - w / 2) ^ 5 at hstrict
    linarith
  · have hsize : I.card = 2 ∨ I.card = 3 := by omega
    have hgamma : (3 / 64 : ℝ) ≤ dittertConstant I.card * dittertConstant (6 - I.card) := by
      rcases hsize with h | h <;> rw [h] <;> norm_num [dittertConstant, Nat.factorial]
    have hfloor := permanent_lower_bound_of_two_blocks A B hA hB q hq hdom I J hcard w hcross hw
    have hsmallfloor := (mul_le_mul_of_nonneg_right hgamma (pow_nonneg hbase 6)).trans hfloor
    have hstrict := nonsingleton_floor_gt_deficit hd0 hdg
    change dittertConstant 6 - (dittertConstant 6 - A.permanent) <
      (3 / 64 : ℝ) * (q - w / 2) ^ 6 at hstrict
    linarith


/-- Every actual order-six global maximum is the uniform matrix, on the full
closed nonnegative simplex. -/
theorem dittert_globalMax_uniform_six (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A) : A = uniformDittertMatrix 6 := by
  by_contra hu
  obtain ⟨I, J, hcard, hlo, hhi, hcross, hext⟩ := dittert_globalMax_cut_six A hA hmass hmax hu
  exact six_balanced_cut_contradiction A hA hmass hmax I J hcard hlo hhi hcross hext

/-- Dittert's inequality and its unique equality case at order six. -/
theorem dittert_order_six : DittertMaximizer 6 :=
  dittertMaximizer_of_globalMax_uniform (by norm_num) dittert_globalMax_uniform_six

end DittertRybin
