import DR.Certificates.FiniteK3QuarticProbability
import DR.ProbabilityScaling
import DR.Uniform

open scoped BigOperators
open DittertRybin DittertRybin.Certificates

-- Repeating just one label does not make the multiplier cells equal.
example : finiteK3MultiplierWeight (![0,0,1,1] : Fin 4 → Fin 2)
    (![0,1,0,1] : Fin 4 → Fin 2) = 1 := by decide +kernel
example : unorderedPairWeight ((0,0) : Fin 2 × Fin 2) (0,1) = 1/2 := by
  norm_num [unorderedPairWeight]

-- A repeated cell has the full diagonal multiplier weight.
example : finiteK3MultiplierWeight (![0,0,1,1] : Fin 4 → Fin 2)
    (![0,0,0,1] : Fin 4 → Fin 2) = 2 := by decide +kernel
example : unorderedPairWeight ((0,0) : Fin 2 × Fin 2) (0,0) = 1 := by
  norm_num [unorderedPairWeight]

-- Inclusive OR counts simultaneous row and column success once.
example : finiteK3DeletedSuccess (![0,1,2,0] : Fin 4 → Fin 3)
    (![0,1,2,0] : Fin 4 → Fin 3) 3 = 1 := by decide +kernel
example : finiteK3DeletedSuccess (![0,1,2,0] : Fin 4 → Fin 3)
    (![0,0,0,0] : Fin 4 → Fin 3) 3 = 1 := by decide +kernel
example : finiteK3DeletedSuccess (![0,0,0,0] : Fin 4 → Fin 3)
    (![0,1,2,0] : Fin 4 → Fin 3) 3 = 1 := by decide +kernel
example : finiteK3DeletedSuccess (![0,0,1,0] : Fin 4 → Fin 3)
    (![0,1,1,0] : Fin 4 → Fin 3) 3 = 0 := by decide +kernel

-- This diagonal check detects losing the factor two before the six-pair average.
example :
    (∑ s : Fin 4 → Fin 1 × Fin 1, sampleMass (fun _ => (-2 : ℝ)) s *
      finiteK3QuartetObservable (fun _ => 1) s) = 32 := by
  rw [sum_finiteK3QuartetObservable]
  norm_num [quadraticValue, finiteK3Entry, unorderedPairWeight,
    Fintype.sum_prod_type, Fin.sum_univ_one]

-- A negative unnormalized board gives S=-2 and F3=-256/81: deletion yields
-- +512/81, detecting either a missing mass factor or an assumed probability law.
example (a : Fin 4) :
    (∑ s : Fin 4 → Fin 3 × Fin 3, sampleMass (fun _ => (-2/9 : ℝ)) s *
      (finiteK3DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) =
      512/81 := by
  have hF : separationProbability (fun _ _ : Fin 3 => (-2/9 : ℝ)) 3 = -256/81 := by
    have h := separationProbability_smul (uniformBoard 3 3) 3 (-2)
    have hboard : (-2 : ℝ) • uniformBoard 3 3 = (fun _ _ : Fin 3 => (-2/9 : ℝ)) := by
      ext i j
      norm_num [uniformBoard]
    rw [hboard, separationProbability_uniform (by omega) (by omega)] at h
    norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial] at h
    simpa only [neg_div] using h
  rw [sum_finiteK3DeletedSuccess]
  change (∑ _ : Fin 3 × Fin 3, (-2/9 : ℝ)) *
    separationProbability (fun _ _ : Fin 3 => (-2/9 : ℝ)) 3 = 512/81
  rw [hF]
  norm_num

-- The actual board identity retains its extra total-mass factor and degree four.
example {m n : ℕ} {alpha : ℝ} {coefficients : Fin 93 → ℝ}
    (h : FiniteK3CoefficientEquations alpha coefficients) (P : Board m n) :
    alpha * totalMass P ^ 4 - totalMass P * separationProbability P 3 =
      ∑ e : Fin m × Fin n, ∑ f : Fin m × Fin n,
        unorderedPairWeight e f * P e.1 e.2 * P f.1 f.2 *
          quadraticValue (finiteK3Entry coefficients e f) (fun a => P a.1 a.2) :=
  finiteK3_quartic_probability_identity h P

-- Zero-dimensional boards also fit the algebraic identity.
example {alpha : ℝ} {coefficients : Fin 93 → ℝ}
    (h : FiniteK3CoefficientEquations alpha coefficients) (P : Board 0 3) :
    alpha * totalMass P ^ 4 - totalMass P * separationProbability P 3 = 0 := by
  rw [finiteK3_quartic_probability_identity h]
  simp

#print axioms finiteK3QuartetObservable_tuple
#print axioms sum_finiteK3QuartetObservable
#print axioms sum_finiteK3PairValue
#print axioms sum_finiteK3DeletedSuccess
#print axioms finiteK3_quartic_event_identity
#print axioms finiteK3_quartic_probability_identity
