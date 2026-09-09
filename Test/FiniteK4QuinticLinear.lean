import DR.Certificates.FiniteK4QuinticLinear
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- Grouping slots does not require distinct role labels: this map is constant.
example (w : Fin 3 → ℝ) (f : Fin 2 → ℝ) :
    (∑ q : Fin 3, w q * f 0) = ∑ k : Fin 2, (∑ q : Fin 3, if (0 : Fin 2) = k then w q else 0) * f k :=
  sum_slot_fibers (fun _ => 0) w f

-- Signed weights cancel before any positivity premise is available.
example : (∑ q : Fin 2, (![(-2 : ℝ),2] q) * (5 : ℝ)) = 0 := by
  norm_num [Fin.sum_univ_two]

-- The full repeated-cell multiplier has ten choices of weight six and one occupied slot.
private def repeatedTerms (k : Fin 10) : Fin 407 × Nat := if k=0 then (0,1) else (0,0)
private theorem repeatedFiber (k : Fin 10) :
    1 * (∑ _q : Fin 10, if (0 : Fin 10)=k then 6 else 0) = 60*(repeatedTerms k).2 := by
  fin_cases k <;> decide +kernel
example (coeff : Fin 407 → ℝ) :
    (1 : ℝ) * (∑ _q : Fin 10, (6 : ℝ) * coeff 0) =
      60 * ∑ k : Fin 10, ((repeatedTerms k).2 : ℝ) * coeff (repeatedTerms k).1 := by
  have h := quintic_sparse_fiber_identity repeatedTerms (fun _ => 0) (fun _ => 6) (fun _ => 0) 1 coeff
    (by intro q; simp [repeatedTerms]) repeatedFiber
  simpa only [Nat.cast_one, Nat.cast_ofNat] using h

-- An occupied padding slot or a lost repeated-cell factor breaks the integer fiber equation.
example : (1 : Nat) * (∑ _q : Fin 10, (1 : Nat)) ≠ 60*1 := by decide +kernel
example : (1 : Nat) * (∑ _q : Fin 10, (0 : Nat)) ≠ 60*1 := by decide +kernel

#print axioms sum_slot_fibers
#print axioms quintic_sparse_fiber_identity
end DittertRybin.Tests
