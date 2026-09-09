import DR.Certificates.FiniteK4QuinticChoice
import DR.Certificates.WeightedTriple
import DR.Certificates.QuinticSampling

/-! Actual signed quintic evaluation from the ten multiplier choices.
The pointwise coefficient identity remains an explicit obligation here;
finite equation data will discharge it separately. -/
namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section

/-- Literal finite-role matrix at an actual multiplier triple and quadratic pair. -/
def finiteK4Entry {m n : ℕ} (coeff : Fin 407 → ℝ)
    (t : Fin 3 → Fin m × Fin n) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  fun a b => coeff (finiteK4RoleIndex
    ![((t 0).1.val,(t 0).2.val),((t 1).1.val,(t 1).2.val),
      ((t 2).1.val,(t 2).2.val),(a.1.val,a.2.val),(b.1.val,b.2.val)])

def finiteK4QuintetObservable {m n : ℕ} (coeff : Fin 407 → ℝ)
    (s : Fin 5 → Fin m × Fin n) : ℝ :=
  (finiteK4MultiplierWeight (fun i => (s i).1) (fun i => (s i).2) : ℝ) *
    coeff (finiteK4RoleIndex (fun i => ((s i).1.val,(s i).2.val)))

def finiteK4TripleValue {m n : ℕ} (coeff : Fin 407 → ℝ)
    (s : Fin 5 → Fin m × Fin n) : ℝ :=
  ∑ q : Fin 10, finiteK4QuintetObservable coeff (s ∘ finiteK4TripleOrder q)

theorem finiteK4QuintetObservable_split {m n : ℕ} (coeff : Fin 407 → ℝ)
    (s : Fin 5 → Fin m × Fin n) :
    finiteK4QuintetObservable coeff s =
      6 * unorderedTripleWeight (fun i => s (Fin.castAdd 2 i)) *
        finiteK4Entry coeff (fun i => s (Fin.castAdd 2 i)) (s 3) (s 4) := by
  have hs : (fun i => ((s i).1.val,(s i).2.val)) =
      ![((s 0).1.val,(s 0).2.val),((s 1).1.val,(s 1).2.val),
        ((s 2).1.val,(s 2).2.val),((s 3).1.val,(s 3).2.val),((s 4).1.val,(s 4).2.val)] := by
    funext i; fin_cases i <;> rfl
  have hw : (finiteK4MultiplierWeight (fun i => (s i).1) (fun i => (s i).2) : ℝ) =
      6 * unorderedTripleWeight (fun i => s (Fin.castAdd 2 i)) := by
    simp only [finiteK4MultiplierWeight, ← Prod.ext_iff]
    change ((if s 0 = s 1 ∧ s 1 = s 2 then 6
      else if s 0 = s 1 ∨ s 0 = s 2 ∨ s 1 = s 2 then 2 else 1 : Nat) : ℝ) =
      6 * (if s 0 = s 1 ∧ s 1 = s 2 then 1
        else if s 0 = s 1 ∨ s 0 = s 2 ∨ s 1 = s 2 then 1/3 else 1/6)
    by_cases ha : s 0 = s 1 ∧ s 1 = s 2 <;>
      by_cases hb : s 0 = s 1 ∨ s 0 = s 2 ∨ s 1 = s 2 <;> norm_num [ha,hb]
  unfold finiteK4QuintetObservable finiteK4Entry
  rw [hw,hs]
  rfl

/-- Six is the ordered-triple correction, including all repeated outcomes. -/
theorem sum_finiteK4QuintetObservable {m n : ℕ} (coeff : Fin 407 → ℝ)
    (p : Fin m × Fin n → ℝ) :
    (∑ s : Fin 5 → Fin m × Fin n, sampleMass p s * finiteK4QuintetObservable coeff s) =
      6 * ∑ t : Fin 3 → Fin m × Fin n, unorderedTripleWeight t * (∏ i, p (t i)) *
        quadraticValue (finiteK4Entry coeff t) p := by
  simp_rw [finiteK4QuintetObservable_split]
  have he (s : Fin 5 → Fin m × Fin n) :
      sampleMass p s * (6 * unorderedTripleWeight (fun i => s (Fin.castAdd 2 i)) *
        finiteK4Entry coeff (fun i => s (Fin.castAdd 2 i)) (s 3) (s 4)) =
      6 * (sampleMass p s * unorderedTripleWeight (fun i => s (Fin.castAdd 2 i)) *
        finiteK4Entry coeff (fun i => s (Fin.castAdd 2 i)) (s 3) (s 4)) := by ring
  simp only [he, ← Finset.mul_sum, sum_sample_five_weighted_quadratic]

/-- Each of the ten position orders has the same actual signed iid sum. -/
theorem sum_finiteK4TripleValue {m n : ℕ} (coeff : Fin 407 → ℝ)
    (p : Fin m × Fin n → ℝ) :
    (∑ s : Fin 5 → Fin m × Fin n, sampleMass p s * finiteK4TripleValue coeff s) =
      60 * ∑ t : Fin 3 → Fin m × Fin n, unorderedTripleWeight t * (∏ i, p (t i)) *
        quadraticValue (finiteK4Entry coeff t) p := by
  have hperm (q : Fin 10) :
      (∑ s : Fin 5 → Fin m × Fin n, sampleMass p s *
        finiteK4QuintetObservable coeff (s ∘ finiteK4TripleOrder q)) =
        ∑ s : Fin 5 → Fin m × Fin n, sampleMass p s * finiteK4QuintetObservable coeff s :=
    sum_sampleMass_permutation p
      (Equiv.ofBijective (finiteK4TripleOrder q) (finiteK4TripleOrder_bijective q)) _
  simp only [finiteK4TripleValue]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_finiteK4QuintetObservable]
  ring

/-- Deleting any one position gives total mass times the literal four-sample success. -/
theorem sum_finiteK4DeletedSuccess {m n : ℕ} (P : Board m n) (a : Fin 5) :
    (∑ s : Fin 5 → Fin m × Fin n, sampleMass (fun e => P e.1 e.2) s *
      (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) =
      totalMass P * separationProbability P 4 := by
  classical
  have h := sum_sampleMass_delete (fun e : Fin m × Fin n => P e.1 e.2) a
    (fun t : Fin 4 → Fin m × Fin n => if RowsDistinct t ∨ ColsDistinct t then (1 : ℝ) else 0)
  rw [sum_cell_weights] at h
  convert! h using 1 <;>
    simp only [finiteK4DeletedSuccess, eventMass, separationProbability, RowsDistinct,
      ColsDistinct, Function.comp_def, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]
  · apply Finset.sum_congr rfl
    intro s _
    by_cases ht : (Function.Injective fun i => (s (a.succAbove i)).1) ∨
        (Function.Injective fun i => (s (a.succAbove i)).2) <;>
      simp only [ht, if_true, if_false, mul_one, mul_zero]
  · congr 1
    apply Finset.sum_congr rfl
    intro s _
    by_cases ht : (Function.Injective fun i => (s i).1) ∨
        (Function.Injective fun i => (s i).2) <;>
      simp only [ht, if_true, if_false, mul_one, mul_zero]

/-- The local identity yields the exact homogeneous gap without dividing by total mass. -/
theorem finiteK4_probability_identity_of_local {m n : ℕ} (alpha : ℝ) (coeff : Fin 407 → ℝ)
    (hloc : ∀ s : Fin 5 → Fin m × Fin n, finiteK4TripleValue coeff s =
      60 * alpha - 12 * (∑ a : Fin 5,
        (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)))
    (P : Board m n) :
    alpha * totalMass P ^ 5 - totalMass P * separationProbability P 4 =
      ∑ t : Fin 3 → Fin m × Fin n, unorderedTripleWeight t * (∏ i, P (t i).1 (t i).2) *
        quadraticValue (finiteK4Entry coeff t) (fun e => P e.1 e.2) := by
  have he := sum_finiteK4TripleValue coeff (fun e => P e.1 e.2)
  have hdel : (∑ s : Fin 5 → Fin m × Fin n, sampleMass (fun e => P e.1 e.2) s *
      (∑ a : Fin 5, (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ))) =
      5 * (totalMass P * separationProbability P 4) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [sum_finiteK4DeletedSuccess, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [hloc, mul_sub] at he
  rw [Finset.sum_sub_distrib] at he
  have hs : (∑ s : Fin 5 → Fin m × Fin n,
      sampleMass (fun e => P e.1 e.2) s * (60 * alpha)) = 60 * alpha * totalMass P ^ 5 := by
    rw [← Finset.sum_mul, sum_sampleMass, sum_cell_weights]
    ring
  have hd : (∑ s : Fin 5 → Fin m × Fin n,
      sampleMass (fun e => P e.1 e.2) s * (12 * ∑ a : Fin 5,
        (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ))) =
      60 * (totalMass P * separationProbability P 4) := by
    simp only [mul_left_comm (sampleMass _ _) 12, ← Finset.mul_sum, hdel]
    ring
  rw [hs,hd] at he
  linarith only [he]

end
end DittertRybin.Certificates
