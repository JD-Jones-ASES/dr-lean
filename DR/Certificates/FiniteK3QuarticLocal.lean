import DR.Certificates.FiniteK3QuarticTemplate
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Exact transfer of the 33 literal coefficient equations to every physical
ordered quartet. This remains a local algebraic identity until summed against
the actual iid mass in the next module. -/

namespace DittertRybin.Certificates
open scoped BigOperators

def FiniteK3CoefficientEquations (alpha : ℝ) (coefficients : Fin 93 → ℝ) : Prop :=
  ∀ a : Fin 33, (∑ k, (((finiteK3QuarticRows.get a).get k : Nat) : ℝ) * coefficients k) =
    (finiteK3QuarticMultiplicity.get a : ℝ) * alpha - (finiteK3QuarticSuccesses.get a : ℝ)

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

noncomputable def finiteK3PairValue (coefficients : Fin 93 → ℝ)
    (r : Fin 4 → α) (c : Fin 4 → β) : ℝ :=
  ∑ q : Fin 6, (finiteK3MultiplierWeight (r ∘ finiteK3PairOrder q)
    (c ∘ finiteK3PairOrder q) : ℝ) *
      coefficients (finiteK3Role (r ∘ finiteK3PairOrder q) (c ∘ finiteK3PairOrder q))

theorem finiteK3PatternPairCoefficient_sum (coefficients : Fin 93 → ℝ) (r c : Fin 15) :
    (∑ k, (finiteK3PatternPairCoefficient r c k : ℝ) * coefficients k) =
      finiteK3PairValue coefficients (fourTuplePatterns r) (fourTuplePatterns c) := by
  simp only [finiteK3PatternPairCoefficient, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, finiteK3PairValue]

set_option maxHeartbeats 2000000 in
theorem finiteK3PairValue_pattern_eq {alpha : ℝ} {coefficients : Fin 93 → ℝ}
    (h : FiniteK3CoefficientEquations alpha coefficients) (r c : Fin 15) :
    finiteK3PairValue coefficients (fourTuplePatterns r) (fourTuplePatterns c) =
      12 * alpha - 3 * (∑ a, (finiteK3DeletedSuccess (fourTuplePatterns r)
        (fourTuplePatterns c) a : ℝ)) := by
  let index := finiteK3PatternEquation r c
  let m : ℝ := finiteK3QuarticMultiplicity.get index
  have hm : m ≠ 0 := by
    dsimp only [m]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (finiteK3QuarticMultiplicity_pos index))
  have hid (k : Fin 93) : m * (finiteK3PatternPairCoefficient r c k : ℝ) =
      12 * (((finiteK3QuarticRows.get index).get k : Nat) : ℝ) := by
    dsimp only [m,index]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun n : Nat => (n : ℝ)) (finiteK3PatternPairCoefficient_identity r c k)
  have hs : m * 3 * (∑ a, (finiteK3DeletedSuccess (fourTuplePatterns r)
        (fourTuplePatterns c) a : ℝ)) = 12 * (finiteK3QuarticSuccesses.get index : ℝ) := by
    dsimp only [m,index]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using
      congrArg (fun n : Nat => (n : ℝ)) (finiteK3PatternDeletedSuccess_identity r c)
  have hsum : m * (∑ k, (finiteK3PatternPairCoefficient r c k : ℝ) * coefficients k) =
      12 * (∑ k, (((finiteK3QuarticRows.get index).get k : Nat) : ℝ) * coefficients k) := by
    simp only [Finset.mul_sum, ← mul_assoc, hid]
  rw [finiteK3PatternPairCoefficient_sum, h index] at hsum
  apply (mul_left_cancel₀ hm)
  change m * finiteK3PairValue coefficients (fourTuplePatterns r) (fourTuplePatterns c) =
    12 * (m * alpha - (finiteK3QuarticSuccesses.get index : ℝ)) at hsum
  nlinarith only [hsum,hs]

theorem finiteK3MultiplierWeight_congr {α' β' : Type*} [DecidableEq α'] [DecidableEq β']
    (r : Fin 4 → α) (c : Fin 4 → β) (r' : Fin 4 → α') (c' : Fin 4 → β')
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j) :
    finiteK3MultiplierWeight r c = finiteK3MultiplierWeight r' c' := by
  simp only [finiteK3MultiplierWeight, hr, hc]

theorem finiteK3DeletedSuccess_congr {α' β' : Type*} [DecidableEq α'] [DecidableEq β']
    (r : Fin 4 → α) (c : Fin 4 → β) (r' : Fin 4 → α') (c' : Fin 4 → β')
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j) (a : Fin 4) :
    finiteK3DeletedSuccess r c a = finiteK3DeletedSuccess r' c' a := by
  have hri : Function.Injective (r ∘ a.succAbove) ↔ Function.Injective (r' ∘ a.succAbove) := by
    simp only [Function.Injective, Function.comp_apply, hr]
  have hci : Function.Injective (c ∘ a.succAbove) ↔ Function.Injective (c' ∘ a.succAbove) := by
    simp only [Function.Injective, Function.comp_apply, hc]
  simp only [finiteK3DeletedSuccess, hri, hci]

theorem finiteK3PairValue_congr {α' β' : Type*} [DecidableEq α'] [DecidableEq β']
    (coefficients : Fin 93 → ℝ) (r : Fin 4 → α) (c : Fin 4 → β)
    (r' : Fin 4 → α') (c' : Fin 4 → β')
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j) :
    finiteK3PairValue coefficients r c = finiteK3PairValue coefficients r' c' := by
  apply Finset.sum_congr rfl
  intro q _
  have hr' (i j : Fin 4) := hr (finiteK3PairOrder q i) (finiteK3PairOrder q j)
  have hc' (i j : Fin 4) := hc (finiteK3PairOrder q i) (finiteK3PairOrder q j)
  rw [finiteK3MultiplierWeight_congr (r ∘ finiteK3PairOrder q) (c ∘ finiteK3PairOrder q)
    (r' ∘ finiteK3PairOrder q) (c' ∘ finiteK3PairOrder q) hr' hc',
    finiteK3Role_congr (r ∘ finiteK3PairOrder q) (c ∘ finiteK3PairOrder q)
    (r' ∘ finiteK3PairOrder q) (c' ∘ finiteK3PairOrder q) hr' hc']

/-- The actual local identity for arbitrary ambient row and column labels. -/
theorem finiteK3PairValue_eq {alpha : ℝ} {coefficients : Fin 93 → ℝ}
    (h : FiniteK3CoefficientEquations alpha coefficients)
    (r : Fin 4 → α) (c : Fin 4 → β) :
    finiteK3PairValue coefficients r c =
      12 * alpha - 3 * (∑ a, (finiteK3DeletedSuccess r c a : ℝ)) := by
  let r' := fourTuplePatterns (fourTuplePatternIndex r)
  let c' := fourTuplePatterns (fourTuplePatternIndex c)
  have hr (i j : Fin 4) : r i = r j ↔ r' i = r' j := (fourTuplePatternIndex_eq_iff r i j).symm
  have hc (i j : Fin 4) : c i = c j ↔ c' i = c' j := (fourTuplePatternIndex_eq_iff c i j).symm
  rw [finiteK3PairValue_congr coefficients r c r' c' hr hc]
  simp_rw [finiteK3DeletedSuccess_congr r c r' c' hr hc]
  exact finiteK3PairValue_pattern_eq h _ _

end DittertRybin.Certificates
