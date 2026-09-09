import DR.Certificates.FiniteK3QuarticLocal
import DR.Certificates.QuarticSampling
import DR.Certificates.WeightedPair
import DR.Semimatching

/-!
# From the finite quartic equations to the actual iid functional

The six position-pair orders each have the same iid weighted sum. A repeated
multiplier cell has integer weight two, and a distinct pair weight one; these
are exactly twice the ordered weights used for an unordered-pair certificate.
The four deleted-success terms each integrate to total mass times the actual
three-sample inclusive-OR event. No sign or normalization assumptions enter.
-/

namespace DittertRybin.Certificates
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The observable attached to the first pair of an actual ordered quartet. -/
noncomputable def finiteK3QuartetObservable (coefficients : Fin 93 → ℝ)
    (s : Fin 4 → α × β) : ℝ :=
  (finiteK3MultiplierWeight (fun i => (s i).1) (fun i => (s i).2) : ℝ) *
    coefficients (finiteK3Role (fun i => (s i).1) (fun i => (s i).2))

omit [Fintype α] [Fintype β] in
theorem finiteK3QuartetObservable_tuple (coefficients : Fin 93 → ℝ)
    (e f a b : α × β) :
    finiteK3QuartetObservable coefficients ![e,f,a,b] =
      2 * unorderedPairWeight e f * finiteK3Entry coefficients e f a b := by
  have hrow : (fun i => (![e,f,a,b] i).1) = ![e.1,f.1,a.1,b.1] := by
    funext i; fin_cases i <;> rfl
  have hcol : (fun i => (![e,f,a,b] i).2) = ![e.2,f.2,a.2,b.2] := by
    funext i; fin_cases i <;> rfl
  unfold finiteK3QuartetObservable
  rw [hrow, hcol]
  have heq : e.1 = f.1 ∧ e.2 = f.2 ↔ e = f := Prod.ext_iff.symm
  simp only [finiteK3MultiplierWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    heq, Nat.cast_ite, Nat.cast_ofNat, Nat.cast_one, finiteK3Entry, unorderedPairWeight]
  by_cases hef : e = f <;> simp [hef]

/-- Expanding four independent positions gives the exact weighted pair quadratic sum. -/
theorem sum_finiteK3QuartetObservable (coefficients : Fin 93 → ℝ) (p : α × β → ℝ) :
    (∑ s : Fin 4 → α × β, sampleMass p s * finiteK3QuartetObservable coefficients s) =
      2 * ∑ e, ∑ f, unorderedPairWeight e f * p e * p f *
        quadraticValue (finiteK3Entry coefficients e f) p := by
  classical
  rw [sum_sample_four]
  simp only [finiteK3QuartetObservable_tuple]
  simp only [quadraticValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [sampleMass, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  ring

/-- All six ordered position-pair choices integrate to the same iid sum. -/
theorem sum_finiteK3PairValue (coefficients : Fin 93 → ℝ) (p : α × β → ℝ) :
    (∑ s : Fin 4 → α × β, sampleMass p s *
      finiteK3PairValue coefficients (fun i => (s i).1) (fun i => (s i).2)) =
      12 * ∑ e, ∑ f, unorderedPairWeight e f * p e * p f *
        quadraticValue (finiteK3Entry coefficients e f) p := by
  classical
  have hperm (q : Fin 6) :
      (∑ s : Fin 4 → α × β, sampleMass p s *
        finiteK3QuartetObservable coefficients (s ∘ finiteK3PairOrder q)) =
        ∑ s : Fin 4 → α × β, sampleMass p s * finiteK3QuartetObservable coefficients s := by
    exact sum_sampleMass_permutation p
      (Equiv.ofBijective (finiteK3PairOrder q) (finiteK3PairOrder_bijective q)) _
  change (∑ s : Fin 4 → α × β, sampleMass p s *
    ∑ q : Fin 6, finiteK3QuartetObservable coefficients (s ∘ finiteK3PairOrder q)) = _
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_finiteK3QuartetObservable]
  ring

/-- Retaining any three positions gives the literal inclusive-OR separation event. -/
theorem sum_finiteK3DeletedSuccess (p : α × β → ℝ) (a : Fin 4) :
    (∑ s : Fin 4 → α × β, sampleMass p s *
      (finiteK3DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) =
      (∑ e, p e) * eventMass p
        {t : Fin 3 → α × β | Function.Injective (fun i => (t i).1) ∨
          Function.Injective (fun i => (t i).2)} := by
  classical
  have h := sum_sampleMass_delete p a
    (fun t : Fin 3 → α × β => if Function.Injective (fun i => (t i).1) ∨
      Function.Injective (fun i => (t i).2) then (1 : ℝ) else 0)
  convert! h using 1 <;>
    simp only [finiteK3DeletedSuccess, eventMass, Function.comp_def,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.mem_ofPred_eq,
      mul_ite, mul_one, mul_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : Function.Injective (fun i => (t i).1) ∨
      Function.Injective (fun i => (t i).2) <;> simp only [ht, if_true, if_false]

/-- The coefficient equations imply the signed, unnormalized quartic event identity. -/
theorem finiteK3_quartic_event_identity {alpha : ℝ} {coefficients : Fin 93 → ℝ}
    (h : FiniteK3CoefficientEquations alpha coefficients) (p : α × β → ℝ) :
    alpha * (∑ e, p e) ^ 4 - (∑ e, p e) * eventMass p
      {t : Fin 3 → α × β | Function.Injective (fun i => (t i).1) ∨
        Function.Injective (fun i => (t i).2)} =
      ∑ e, ∑ f, unorderedPairWeight e f * p e * p f *
        quadraticValue (finiteK3Entry coefficients e f) p := by
  classical
  have hlocal := sum_finiteK3PairValue coefficients p
  have hdeleted :
      (∑ s : Fin 4 → α × β, sampleMass p s *
        ∑ a, (finiteK3DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) =
        4 * ((∑ e, p e) * eventMass p
          {t : Fin 3 → α × β | Function.Injective (fun i => (t i).1) ∨
            Function.Injective (fun i => (t i).2)}) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [sum_finiteK3DeletedSuccess]
    simp
  simp_rw [finiteK3PairValue_eq h] at hlocal
  have hconstant : (∑ s : Fin 4 → α × β, sampleMass p s * (12 * alpha)) =
      12 * alpha * (∑ e, p e) ^ 4 := by
    rw [← Finset.sum_mul, sum_sampleMass]
    ring
  have hsplit : (∑ s : Fin 4 → α × β, sampleMass p s *
      (12 * alpha - 3 * ∑ a,
        (finiteK3DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ))) =
      12 * alpha * (∑ e, p e) ^ 4 -
        3 * (∑ s : Fin 4 → α × β, sampleMass p s * ∑ a,
          (finiteK3DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) := by
    rw [Finset.mul_sum]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hconstant]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsplit, hdeleted] at hlocal
  linarith only [hlocal]

/-- The same identity for the actual board functional, with no probability premise. -/
theorem finiteK3_quartic_probability_identity {m n : ℕ} {alpha : ℝ}
    {coefficients : Fin 93 → ℝ} (h : FiniteK3CoefficientEquations alpha coefficients)
    (P : Board m n) :
    alpha * totalMass P ^ 4 - totalMass P * separationProbability P 3 =
      ∑ e : Fin m × Fin n, ∑ f : Fin m × Fin n,
        unorderedPairWeight e f * P e.1 e.2 * P f.1 f.2 *
          quadraticValue (finiteK3Entry coefficients e f) (fun a => P a.1 a.2) := by
  simpa only [sum_cell_weights, separationProbability, RowsDistinct, ColsDistinct] using
    finiteK3_quartic_event_identity h (fun a : Fin m × Fin n => P a.1 a.2)

end DittertRybin.Certificates
