import DR.Certificates.QuarticSampling
import Mathlib.Tactic.NormNum

open scoped BigOperators
open DittertRybin

-- No positivity or mass-one premise is used by coordinate exchangeability.
example {α : Type*} [Fintype α] (p : α → ℝ) (f : (Fin 4 → α) → ℝ) :
    (∑ s : Fin 4 → α, sampleMass p s * f (s ∘ Equiv.swap 0 3)) =
      ∑ s : Fin 4 → α, sampleMass p s * f s :=
  sum_sampleMass_permutation p (Equiv.swap 0 3) f

-- A negative total mass contributes its sign, even with an empty retained sample.
example :
    (∑ s : Fin 1 → Fin 2, sampleMass (![2,-3] : Fin 2 → ℝ) s * (7 : ℝ)) = -7 := by
  have h := sum_sampleMass_delete (![2,-3] : Fin 2 → ℝ) (0 : Fin 1)
    (fun _ : Fin 0 → Fin 2 => (7 : ℝ))
  norm_num [Fin.sum_univ_two] at h
  exact h

-- Zero total mass needs no division or exceptional case, for any retained observable.
example (a : Fin 4) (f : (Fin 3 → Fin 2) → ℝ) :
    (∑ s : Fin 4 → Fin 2, sampleMass (![2,-2] : Fin 2 → ℝ) s * f (s ∘ a.succAbove)) = 0 := by
  have h := sum_sampleMass_delete (![2,-2] : Fin 2 → ℝ) a f
  simpa [Fin.sum_univ_two] using h

-- Empty outcome types are permitted; there is no hidden inhabitance assumption.
example (a : Fin 4) (p : Fin 0 → ℝ) (f : (Fin 3 → Fin 0) → ℝ) :
    (∑ s : Fin 4 → Fin 0, sampleMass p s * f (s ∘ a.succAbove)) = 0 := by
  rw [sum_sampleMass_delete]
  simp

-- The four-position expansion is exact for an arbitrary signed observable.
example {α : Type*} [Fintype α] (f : (Fin 4 → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := sum_sample_four f

#print axioms sampleMass_permutation
#print axioms sum_sampleMass_permutation
#print axioms sum_sampleMass_delete
#print axioms sum_sample_four
