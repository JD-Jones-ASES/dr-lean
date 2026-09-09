import DR.Rectangular.ThreeRowAveraging
import DR.Rectangular.OrderThreeLargeBounds
import DR.Maximizers

/-!
# Compact support-preserving classes of global maximizers

The original zeros are fixed, and every other entry has a fixed positive lower
bound. This makes same-support averaging available throughout a compact class;
no zero pattern is silently replaced by a larger allowed mask.
-/

namespace DittertRybin
open scoped BigOperators

/-- Preserve every original zero and a uniform lower bound on every original positive entry. -/
def SameSupportFloor {m n : ℕ} (P : Board m n) (ε : ℝ) (Q : Board m n) : Prop :=
  ∀ i j, (P i j = 0 → Q i j = 0) ∧ (0 < P i j → ε ≤ Q i j)

theorem SameSupportFloor.support_iff {m n : ℕ} {P Q : Board m n} {ε : ℝ}
    (h : SameSupportFloor P ε Q) (hP : ∀ i j, 0 ≤ P i j) (hε : 0 < ε)
    (i : Fin m) (j : Fin n) : 0 < Q i j ↔ 0 < P i j := by
  constructor
  · intro hQ
    by_contra hnot
    have hz : P i j = 0 := le_antisymm (le_of_not_gt hnot) (hP i j)
    rw [(h i j).1 hz] at hQ
    exact lt_irrefl _ hQ
  · intro hpos
    exact hε.trans_le ((h i j).2 hpos)

theorem isClosed_sameSupportFloor {m n : ℕ} (P : Board m n) (ε : ℝ) :
    IsClosed {Q : Board m n | SameSupportFloor P ε Q} := by
  simp only [SameSupportFloor, Set.ofPred_forall, Set.ofPred_and]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply IsClosed.inter
  · apply isClosed_iInter
    intro _hzero
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · apply isClosed_iInter
    intro _hpos
    exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))

/-- The compact class keeps the value of the given global maximizer exactly. -/
def supportedMaximizerSet {m n : ℕ} (P : Board m n) (k : ℕ) (ε : ℝ) : Set (Board m n) :=
  {Q | IsProbability Q ∧ separationProbability Q k = separationProbability P k ∧ SameSupportFloor P ε Q}

theorem isCompact_supportedMaximizerSet {m n : ℕ} (P : Board m n) (k : ℕ) (ε : ℝ) :
    IsCompact (supportedMaximizerSet P k ε) := by
  exact (isCompact_probabilitySimplex m n).inter_right
    ((isClosed_eq (continuous_separationProbability k) continuous_const).inter
      (isClosed_sameSupportFloor P ε))

theorem IsSeparationGlobalMax.of_value_eq {m n k : ℕ} {P Q : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hvalue : separationProbability Q k = separationProbability P k) :
    IsSeparationGlobalMax Q k := by
  intro R hR
  exact (hmax R hR).trans_eq hvalue.symm

theorem IsSeparationGlobalMax.transpose {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) : IsSeparationGlobalMax P.transpose k := by
  intro Q hQ
  simpa only [separationProbability_transpose] using hmax Q.transpose hQ.transpose

theorem continuous_orderThreeSquareSum {m n : ℕ} :
    Continuous (fun P : Board m n => orderThreeSquareSum P) := by
  unfold orderThreeSquareSum
  fun_prop

/-- Every nonempty closed support class has an actual least-norm maximizer. -/
theorem exists_least_norm_supportedMaximizer {m n k : ℕ} {P : Board m n} {ε : ℝ}
    (hP : IsProbability P) (hfloor : SameSupportFloor P ε P) :
    ∃ Q ∈ supportedMaximizerSet P k ε, ∀ R ∈ supportedMaximizerSet P k ε,
      orderThreeSquareSum Q ≤ orderThreeSquareSum R := by
  exact (isCompact_supportedMaximizerSet P k ε).exists_isMinOn
    ⟨P, hP, rfl, hfloor⟩ continuous_orderThreeSquareSum.continuousOn

/-- Midpoint averaging lowers the actual squared Frobenius norm by half the pair distance. -/
theorem orderThreeSquareSum_blend_midpoint {m n : ℕ} (P : Board m n)
    (a b : Fin n) (hab : a ≠ b) :
    orderThreeSquareSum (blendColumns P a b (1 / 2)) = orderThreeSquareSum P -
      (1 / 2) * ∑ i, (P i a - P i b) ^ 2 := by
  have hterm (i : Fin m) (j : Fin n) : blendColumns P a b (1 / 2) i j ^ 2 = P i j ^ 2 +
      (if j = a then ((P i a + P i b) / 2) ^ 2 - P i a ^ 2 else 0) +
      (if j = b then ((P i a + P i b) / 2) ^ 2 - P i b ^ 2 else 0) := by
    by_cases ha : j = a <;> by_cases hb : j = b <;> simp_all [blendColumns] <;> ring
  have hrow (i : Fin m) : (∑ j, blendColumns P a b (1 / 2) i j ^ 2) =
      (∑ j, P i j ^ 2) - (1 / 2) * (P i a - P i b) ^ 2 := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp only [orderThreeSquareSum, hrow, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Equal actual support makes the fixed positive floor invariant under a column blend. -/
theorem SameSupportFloor.blendColumns {m n : ℕ} {P Q : Board m n} {ε t : ℝ}
    (hfloor : SameSupportFloor P ε Q) (hP : ∀ i j, 0 ≤ P i j)
    (a b : Fin n) (hab : a ≠ b) (hsupport : ∀ i, 0 < P i a ↔ 0 < P i b)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : SameSupportFloor P ε (blendColumns Q a b t) := by
  have hzero (i : Fin m) : P i a = 0 ↔ P i b = 0 := by
    constructor
    · intro ha
      apply le_antisymm _ (hP i b)
      by_contra hb
      have hpos : 0 < P i b := lt_of_not_ge hb
      have h := (hsupport i).mpr hpos
      exact (ne_of_gt h) ha
    · intro hb
      apply le_antisymm _ (hP i a)
      by_contra ha
      have hpos : 0 < P i a := lt_of_not_ge ha
      have h := (hsupport i).mp hpos
      exact (ne_of_gt h) hb
  intro i j
  by_cases hja : j = a
  · subst j
    constructor
    · intro hz
      rw [blendColumns_left, (hfloor i a).1 hz, (hfloor i b).1 ((hzero i).mp hz)]
      ring
    · intro hp
      exact blendColumns_entry_lower a b ht ht1 i ((hfloor i a).2 hp)
        ((hfloor i b).2 ((hsupport i).mp hp))
  · by_cases hjb : j = b
    · subst j
      constructor
      · intro hz
        rw [blendColumns_right Q a b hab, (hfloor i a).1 ((hzero i).mpr hz), (hfloor i b).1 hz]
        ring
      · intro hp
        rw [blendColumns_right Q a b hab]
        have h1 := mul_le_mul_of_nonneg_left ((hfloor i a).2 ((hsupport i).mpr hp)) ht
        have h2 := mul_le_mul_of_nonneg_left ((hfloor i b).2 hp) (sub_nonneg.mpr ht1)
        nlinarith only [h1, h2]
    · simpa only [DittertRybin.blendColumns, if_neg hja, if_neg hjb] using hfloor i j

end DittertRybin
