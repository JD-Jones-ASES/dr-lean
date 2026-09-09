import DR.Certificates.QuinticSampling
import DR.ProbabilityScaling
import DR.Uniform

open DittertRybin DittertRybin.Certificates
open scoped BigOperators

-- The permutation factor remains 5! when every outcome is repeated.
example (p : Fin 1 → ℝ) (f : (Fin 5 → Fin 1) → ℝ) :
    (∑ s, sampleMass p s * ∑ σ : Equiv.Perm (Fin 5), f (s ∘ σ)) =
      120 * ∑ s, sampleMass p s * f s := by
  have hfac : (Nat.factorial 5 : ℝ) = 120 := by norm_num [Nat.factorial]
  simpa only [hfac] using sum_sampleMass_symmetrize p f

-- Empty outcome types and the unique empty sample are included.
example (p : Fin 0 → ℝ) (f : (Fin 0 → Fin 0) → ℝ) :
    (∑ s, sampleMass p s * ∑ σ : Equiv.Perm (Fin 0), f (s ∘ σ)) =
      ∑ s, sampleMass p s * f s := by
  rw [sum_sampleMass_symmetrize]
  norm_num

private theorem negative_uniform_mass :
    totalMass ((-2 : ℝ) • uniformBoard 5 5) = -2 := by
  norm_num [totalMass, rowSum, uniformBoard, Fin.sum_univ_succ]

-- A negative uniform board has negative fifth-degree mass, while F4 scales
-- positively. The extra S is needed for exact cancellation.
example :
    (∑ s : Fin 5 → Fin 5 × Fin 5,
      sampleMass (fun a => ((-2 : ℝ) • uniformBoard 5 5) a.1 a.2) s *
        quinticGapObservable (separationProbability (uniformBoard 5 5) 4) s) = 0 := by
  rw [sum_quinticGapObservable, negative_uniform_mass, separationProbability_smul]
  ring

example :
    separationProbability (uniformBoard 5 5) 4 *
      totalMass ((-2 : ℝ) • uniformBoard 5 5) ^ 5 -
      separationProbability ((-2 : ℝ) • uniformBoard 5 5) 4 ≠ 0 := by
  rw [negative_uniform_mass, separationProbability_smul,
    separationProbability_uniform (by decide) (by decide)]
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

-- No fictitious probability hypothesis is needed on the empty rectangle.
example (P : Board 0 7) (alpha : ℝ) :
    (∑ s : Fin 5 → Fin 0 × Fin 7,
      sampleMass (fun a => P a.1 a.2) s * quinticGapObservable alpha s) = 0 := by
  rw [sum_quinticGapObservable]
  simp [totalMass]

#print axioms sum_sampleMass_symmetrize
#print axioms sum_sampleMass_eq_of_permutation_sums
#print axioms sum_quinticGapObservable
