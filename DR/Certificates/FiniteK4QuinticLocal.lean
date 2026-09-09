import DR.Certificates.FiniteK4QuinticTemplate
import DR.Certificates.FiniteK4QuinticLinear
import DR.Certificates.FiniteK4QuinticSampling
import Mathlib.Tactic.Linarith

/-! Exact transfer from one sparse monomial equation and its literal
pattern gates to the physical ten-choice local identity. -/
namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def finiteK4QuinticRowValue (coeff : Fin 407 → ℝ) (a : Fin 91) : ℝ :=
  ∑ k : Fin 10, ((finiteK4QuinticTerm a k).2 : ℝ) * coeff (finiteK4QuinticTerm a k).1

def FiniteK4CoefficientEquations (alpha : ℝ) (coeff : Fin 407 → ℝ) : Prop :=
  ∀ a : Fin 91, finiteK4QuinticRowValue coeff a =
    (finiteK4QuinticMultiplicity.get a : ℝ) * alpha - (finiteK4QuinticSuccesses.get a : ℝ)

def finiteK4PatternSample (r c : Fin 52) (i : Fin 5) : Fin 5 × Fin 5 :=
  (fiveTuplePatterns r i, fiveTuplePatterns c i)

theorem fiveTuplePatternIndex_val (s : Fin 5 → Fin 5) :
    fiveTuplePatternIndex (fun i => (s i).val) = fiveTuplePatternIndex s := by
  apply fiveTuplePatternIndex_congr
  intro i j
  exact Fin.ext_iff.symm

theorem finiteK4QuinticOrderedRole (r c : Fin 52) (q : Fin 10)
    (hdata : FiniteK4QuinticPatternCorrect r c) :
    finiteK4RoleIndex (fun i => ((finiteK4PatternSample r c (finiteK4TripleOrder q i)).1.val,
      (finiteK4PatternSample r c (finiteK4TripleOrder q i)).2.val)) = finiteK4QuinticRole r c q := by
  unfold finiteK4RoleIndex finiteK4PatternSample
  change (finiteK4RoleTable.get
    (fiveTuplePatternIndex (fun i => ((fiveTuplePatterns r ∘ finiteK4TripleOrder q) i).val))).get
    (fiveTuplePatternIndex (fun i => ((fiveTuplePatterns c ∘ finiteK4TripleOrder q) i).val)) = _
  rw [fiveTuplePatternIndex_val (fiveTuplePatterns r ∘ finiteK4TripleOrder q),
    fiveTuplePatternIndex_val (fiveTuplePatterns c ∘ finiteK4TripleOrder q),
    finiteK4QuinticOrderedPattern_index, finiteK4QuinticOrderedPattern_index]
  exact hdata.1 q

theorem finiteK4TripleValue_pattern_table (coeff : Fin 407 → ℝ) (r c : Fin 52)
    (hdata : FiniteK4QuinticPatternCorrect r c) :
    finiteK4TripleValue coeff (finiteK4PatternSample r c) =
      ∑ q : Fin 10, (finiteK4QuinticWeight r c q : ℝ) * coeff (finiteK4QuinticRole r c q) := by
  unfold finiteK4TripleValue
  apply Finset.sum_congr rfl
  intro q _
  unfold finiteK4QuintetObservable
  simp only [Function.comp_apply]
  rw [finiteK4QuinticOrderedRole r c q hdata]
  change (finiteK4MultiplierWeight (fiveTuplePatterns r ∘ finiteK4TripleOrder q)
    (fiveTuplePatterns c ∘ finiteK4TripleOrder q) : ℝ) * _ = _
  rw [hdata.2.1 q]

theorem finiteK4TripleValue_pattern_eq {alpha : ℝ} {coeff : Fin 407 → ℝ}
    (r c : Fin 52) (hdata : FiniteK4QuinticPatternCorrect r c)
    (hrow : finiteK4QuinticRowValue coeff (finiteK4QuinticEquation r c) =
      (finiteK4QuinticMultiplicity.get (finiteK4QuinticEquation r c) : ℝ) * alpha -
        (finiteK4QuinticSuccesses.get (finiteK4QuinticEquation r c) : ℝ)) :
    finiteK4TripleValue coeff (finiteK4PatternSample r c) =
      60 * alpha - 12 * (∑ a : Fin 5,
        (finiteK4DeletedSuccess (fiveTuplePatterns r) (fiveTuplePatterns c) a : ℝ)) := by
  let a := finiteK4QuinticEquation r c
  let m : ℝ := finiteK4QuinticMultiplicity.get a
  have hm : m ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (finiteK4QuinticMultiplicity_pos a))
  have hlin := quintic_sparse_fiber_identity (finiteK4QuinticTerm a)
    (finiteK4QuinticRole r c) (finiteK4QuinticWeight r c) (finiteK4QuinticSlot r c)
    (finiteK4QuinticMultiplicity.get a) coeff hdata.2.2.1 hdata.2.2.2.1
  change m * (∑ q : Fin 10, (finiteK4QuinticWeight r c q : ℝ) * coeff (finiteK4QuinticRole r c q)) =
    60 * finiteK4QuinticRowValue coeff a at hlin
  rw [← finiteK4TripleValue_pattern_table coeff r c hdata, hrow] at hlin
  have hdel : m * 12 * (∑ a : Fin 5,
      (finiteK4DeletedSuccess (fiveTuplePatterns r) (fiveTuplePatterns c) a : ℝ)) =
      60 * (finiteK4QuinticSuccesses.get (finiteK4QuinticEquation r c) : ℝ) := by
    have h := hdata.2.2.2.2.2
    rw [← hdata.2.2.2.2.1] at h
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, m, a] using
      congrArg (fun k : Nat => (k : ℝ)) h
  apply mul_left_cancel₀ hm
  dsimp only [m,a] at hlin hdel ⊢
  nlinarith only [hlin,hdel]

/-- Independent equality patterns suffice across arbitrary physical row and column counts. -/
theorem finiteK4TripleValue_congr {m n m' n' : ℕ} (coeff : Fin 407 → ℝ)
    (s : Fin 5 → Fin m × Fin n) (t : Fin 5 → Fin m' × Fin n')
    (hr : ∀ i j, (s i).1 = (s j).1 ↔ (t i).1 = (t j).1)
    (hc : ∀ i j, (s i).2 = (s j).2 ↔ (t i).2 = (t j).2) :
    finiteK4TripleValue coeff s = finiteK4TripleValue coeff t := by
  unfold finiteK4TripleValue
  apply Finset.sum_congr rfl
  intro q _
  unfold finiteK4QuintetObservable
  have hw := finiteK4MultiplierWeight_congr
    (fun i => (s (finiteK4TripleOrder q i)).1) (fun i => (s (finiteK4TripleOrder q i)).2)
    (fun i => (t (finiteK4TripleOrder q i)).1) (fun i => (t (finiteK4TripleOrder q i)).2)
    (fun i j => hr _ _) (fun i j => hc _ _)
  have hi := finiteK4RoleIndex_congr
    (fun i => ((s (finiteK4TripleOrder q i)).1.val,(s (finiteK4TripleOrder q i)).2.val))
    (fun i => ((t (finiteK4TripleOrder q i)).1.val,(t (finiteK4TripleOrder q i)).2.val))
    (fun i j => Fin.ext_iff.symm.trans ((hr _ _).trans Fin.ext_iff))
    (fun i j => Fin.ext_iff.symm.trans ((hc _ _).trans Fin.ext_iff))
  simp only [Function.comp_apply]
  rw [hw,hi]

/-- A physical tuple uses only its own monomial equation; this supports restricted board families. -/
theorem finiteK4TripleValue_eq_of_pattern {m n : ℕ} {alpha : ℝ} {coeff : Fin 407 → ℝ}
    (s : Fin 5 → Fin m × Fin n)
    (hdata : FiniteK4QuinticPatternCorrect (fiveTuplePatternIndex (fun i => (s i).1))
      (fiveTuplePatternIndex (fun i => (s i).2)))
    (hrow : finiteK4QuinticRowValue coeff (finiteK4QuinticEquation
        (fiveTuplePatternIndex (fun i => (s i).1)) (fiveTuplePatternIndex (fun i => (s i).2))) =
      (finiteK4QuinticMultiplicity.get (finiteK4QuinticEquation
        (fiveTuplePatternIndex (fun i => (s i).1)) (fiveTuplePatternIndex (fun i => (s i).2))) : ℝ) * alpha -
      (finiteK4QuinticSuccesses.get (finiteK4QuinticEquation
        (fiveTuplePatternIndex (fun i => (s i).1)) (fiveTuplePatternIndex (fun i => (s i).2))) : ℝ)) :
    finiteK4TripleValue coeff s = 60 * alpha - 12 * (∑ a : Fin 5,
      (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) := by
  let r := fiveTuplePatternIndex (fun i => (s i).1)
  let c := fiveTuplePatternIndex (fun i => (s i).2)
  have hr (i j : Fin 5) : (s i).1 = (s j).1 ↔ fiveTuplePatterns r i = fiveTuplePatterns r j :=
    (fiveTuplePatternIndex_eq_iff (fun i => (s i).1) i j).symm
  have hc (i j : Fin 5) : (s i).2 = (s j).2 ↔ fiveTuplePatterns c i = fiveTuplePatterns c j :=
    (fiveTuplePatternIndex_eq_iff (fun i => (s i).2) i j).symm
  rw [finiteK4TripleValue_congr coeff s (finiteK4PatternSample r c) hr hc]
  simp_rw [finiteK4DeletedSuccess_congr (fun i => (s i).1) (fun i => (s i).2)
    (fiveTuplePatterns r) (fiveTuplePatterns c) hr hc]
  exact finiteK4TripleValue_pattern_eq r c hdata hrow

end
end DittertRybin.Certificates
