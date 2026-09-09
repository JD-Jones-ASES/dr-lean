import DR.Rectangular.FourRowFinitePolynomial

/-!
# Exact five-sample symmetrization

A quintic coefficient identity can be checked by summing its contribution
over all 120 permutations of five positions. Repeated cells cause no
exception: their equal terms are counted with the same multiplicity on
both sides. This finite-group identity supplies the semantic reduction
from complete equality-pattern checks to the actual polynomial identity.
-/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial
noncomputable section

def fourRowFiniteSamplePermutation {n k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (Fin k → FourRowFiniteCell n) ≃ (Fin k → FourRowFiniteCell n) where
  toFun s := s ∘ σ
  invFun s := s ∘ σ.symm
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

theorem fourRowFiniteSampleMonomial_permute {n k : ℕ}
    (s : Fin k → FourRowFiniteCell n) (σ : Equiv.Perm (Fin k)) :
    fourRowFiniteSampleMonomial (s ∘ σ) = fourRowFiniteSampleMonomial s :=
  Equiv.prod_comp σ (fun t => X (s t))

def fourRowFiniteWeightedPolynomial {n : ℕ}
    (f : (Fin 5 → FourRowFiniteCell n) → ℚ) : MvPolynomial (FourRowFiniteCell n) ℚ :=
  ∑ s, C (f s) * fourRowFiniteSampleMonomial s

theorem fourRowFiniteWeightedPolynomial_permute {n : ℕ}
    (f : (Fin 5 → FourRowFiniteCell n) → ℚ) (σ : Equiv.Perm (Fin 5)) :
    fourRowFiniteWeightedPolynomial (fun s => f (s ∘ σ)) =
      fourRowFiniteWeightedPolynomial f := by
  unfold fourRowFiniteWeightedPolynomial
  apply Fintype.sum_equiv (fourRowFiniteSamplePermutation σ)
  intro s
  change C (f (s ∘ σ)) * fourRowFiniteSampleMonomial s =
    C (f (s ∘ σ)) * fourRowFiniteSampleMonomial (s ∘ σ)
  rw [fourRowFiniteSampleMonomial_permute]

/-- The factor is 120 even when the physical cell multiset has repetitions. -/
theorem fourRowFiniteWeightedPolynomial_symmetrize {n : ℕ}
    (f : (Fin 5 → FourRowFiniteCell n) → ℚ) :
    fourRowFiniteWeightedPolynomial (fun s => ∑ σ : Equiv.Perm (Fin 5), f (s ∘ σ)) =
      120 * fourRowFiniteWeightedPolynomial f := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin 5),
        fourRowFiniteWeightedPolynomial (fun s => f (s ∘ σ)) := by
      simp only [fourRowFiniteWeightedPolynomial, map_sum, Finset.sum_mul]
      exact Finset.sum_comm
    _ = _ := by
      simp only [fourRowFiniteWeightedPolynomial_permute, Finset.sum_const,
        Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      norm_num [Nat.factorial]

/-- A fully checked position-permutation sum gives a genuine polynomial zero. -/
theorem fourRowFiniteWeightedPolynomial_eq_zero_of_permutation_sums {n : ℕ}
    (f : (Fin 5 → FourRowFiniteCell n) → ℚ)
    (h : ∀ s, (∑ σ : Equiv.Perm (Fin 5), f (s ∘ σ)) = 0) :
    fourRowFiniteWeightedPolynomial f = 0 := by
  have he := fourRowFiniteWeightedPolynomial_symmetrize f
  simp only [h, fourRowFiniteWeightedPolynomial, map_zero, zero_mul,
    Finset.sum_const_zero] at he
  have hz : (120 : MvPolynomial (FourRowFiniteCell n) ℚ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp he.symm).resolve_left hz

/-- Equality is certified by finite symmetrized contributions, not by sample evaluation. -/
theorem fourRowFiniteWeightedPolynomial_eq_of_permutation_sums {n : ℕ}
    (f g : (Fin 5 → FourRowFiniteCell n) → ℚ)
    (h : ∀ s, (∑ σ : Equiv.Perm (Fin 5), f (s ∘ σ)) =
      ∑ σ : Equiv.Perm (Fin 5), g (s ∘ σ)) :
    fourRowFiniteWeightedPolynomial f = fourRowFiniteWeightedPolynomial g := by
  have hz := fourRowFiniteWeightedPolynomial_eq_zero_of_permutation_sums (fun s => f s - g s)
    (fun s => by simp only [Finset.sum_sub_distrib, h, sub_self])
  simpa only [fourRowFiniteWeightedPolynomial, map_sub, sub_mul,
    Finset.sum_sub_distrib, sub_eq_zero] using hz

end
end DittertRybin
