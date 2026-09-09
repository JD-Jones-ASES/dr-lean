import DR.Probability
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Ring

/-!
# Marginalizing independent samples

Selecting distinct sample coordinates leaves the same independent sampling
law on the selected coordinates. The proof splits an assignment into its
selected coordinates and their complement, factors the product weight,
and sums the complementary factor to one.

Only normalization is needed for these algebraic identities: weights may
be signed, and either the selected or complementary coordinate type may
be empty. Positivity is needed only when interpreting the weights as
probabilities, as specified in `DR.Probability`.
-/

namespace DittertRybin

open scoped BigOperators

variable {α : Type*} [Fintype α] {k ℓ : ℕ}

/-- Split a sample into its selected coordinates and the complementary coordinates. -/
noncomputable def sampleSplitEquiv (e : Fin ℓ ↪ Fin k) :
    (Fin k → α) ≃ (Fin ℓ → α) × ({j : Fin k // j ∉ Set.range e} → α) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun j => j ∈ Set.range e) (fun _ => α)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm (Equiv.refl α))
      (Equiv.refl _))

omit [Fintype α] in
@[simp] theorem sampleSplitEquiv_fst (e : Fin ℓ ↪ Fin k) (s : Fin k → α) :
    (sampleSplitEquiv e s).1 = s ∘ e := rfl

omit [Fintype α] in
@[simp] theorem sampleSplitEquiv_snd (e : Fin ℓ ↪ Fin k) (s : Fin k → α)
    (j : {j : Fin k // j ∉ Set.range e}) : (sampleSplitEquiv e s).2 j = s j := rfl

open Classical in
omit [Fintype α] in
/-- The full sample weight factors into selected and complementary weights. -/
theorem sampleMass_split (p : α → ℝ) (e : Fin ℓ ↪ Fin k) (s : Fin k → α) :
    sampleMass p s = sampleMass p (s ∘ e) *
      ∏ j : {j : Fin k // j ∉ Set.range e}, p (s j) := by
  rw [sampleMass, ← Fintype.prod_subtype_mul_prod_subtype
    (fun j => j ∈ Set.range e) (fun j => p (s j))]
  congr 1
  exact (Equiv.prod_comp (Equiv.ofInjective e e.injective)
    (fun j : Set.range e => p (s j))).symm

/-- Product weights sum to one over any finite coordinate type. -/
theorem sum_prod_weights_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (p : α → ℝ)
    (hp : ∑ a, p a = 1) : (∑ s : ι → α, ∏ i, p (s i)) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [hp]

/-- An arbitrary weighted observable on distinct selected coordinates has its smaller-sample sum. -/
theorem sum_sampleMass_restrict (p : α → ℝ) (hp : ∑ a, p a = 1)
    (e : Fin ℓ ↪ Fin k) (f : (Fin ℓ → α) → ℝ) :
    (∑ s : Fin k → α, sampleMass p s * f (s ∘ e)) =
      ∑ t : Fin ℓ → α, sampleMass p t * f t := by
  classical
  calc
    _ = ∑ q : (Fin ℓ → α) × ({j : Fin k // j ∉ Set.range e} → α),
        (sampleMass p q.1 * ∏ j, p (q.2 j)) * f q.1 := by
      apply Fintype.sum_equiv (sampleSplitEquiv e)
      intro s
      rw [sampleMass_split p e s]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      calc
        _ = (sampleMass p t * f t) *
            ∑ u : {j : Fin k // j ∉ Set.range e} → α, ∏ j, p (u j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = _ := by
          rw [sum_prod_weights_eq_one (ι := {j : Fin k // j ∉ Set.range e}) p hp,
            mul_one]

/-- Pulling an event back along an injective coordinate selection preserves its mass. -/
theorem eventMass_restrict (p : α → ℝ) (hp : ∑ a, p a = 1)
    (e : Fin ℓ ↪ Fin k) (E : Set (Fin ℓ → α)) :
    eventMass p {s : Fin k → α | (s ∘ e) ∈ E} = eventMass p E := by
  classical
  have h := sum_sampleMass_restrict p hp e (fun t => if t ∈ E then 1 else 0)
  simpa [eventMass, mul_ite] using h

/-- The same marginalization rule for an injective function without a bundled embedding. -/
theorem eventMass_comp_of_injective (p : α → ℝ) (hp : ∑ a, p a = 1)
    (e : Fin ℓ → Fin k) (he : Function.Injective e) (E : Set (Fin ℓ → α)) :
    eventMass p {s : Fin k → α | (s ∘ e) ∈ E} = eventMass p E :=
  eventMass_restrict p hp ⟨e, he⟩ E

@[simp] theorem eventMass_singleton (p : α → ℝ) (t : Fin k → α) :
    eventMass p {t} = sampleMass p t := by
  classical
  simp [eventMass]

/-- Prescribing values on distinct sample coordinates has the product of their individual weights. -/
theorem eventMass_restrict_eq (p : α → ℝ) (hp : ∑ a, p a = 1)
    (e : Fin ℓ ↪ Fin k) (t : Fin ℓ → α) :
    eventMass p {s : Fin k → α | s ∘ e = t} = sampleMass p t := by
  simpa using eventMass_restrict p hp e {t}

end DittertRybin
