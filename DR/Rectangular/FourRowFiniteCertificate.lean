import DR.Rectangular.FourRowFiniteSymmetrization
import DR.Maximizers

/-!
# The exact ordered-triple form of a quintic certificate

Each unordered multiplier is represented by all its orders with correction
1, 1/3 or 1/6 according to its repeated cells. These factors are strictly
positive. Evaluation is a sum of the literal quadratic matrix values, and
a positive repeated-cell multiplier detects every nonuniform boundary board.
The actual catalog, matrix gates and full coefficient identity are separate
obligations, not hypotheses of a claimed endpoint theorem in this module.
-/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial Certificates
noncomputable section

def fourRowFiniteTripleWeight {n : ℕ} (m : Fin 3 → FourRowFiniteCell n) : ℚ :=
  if m 0 = m 1 ∧ m 1 = m 2 then 1
  else if m 0 = m 1 ∨ m 0 = m 2 ∨ m 1 = m 2 then 1/3 else 1/6

theorem fourRowFiniteTripleWeight_pos {n : ℕ} (m : Fin 3 → FourRowFiniteCell n) :
    0 < fourRowFiniteTripleWeight m := by
  unfold fourRowFiniteTripleWeight
  split_ifs <;> norm_num

theorem fourRowFiniteTripleWeight_repeat {n : ℕ} (a : FourRowFiniteCell n) :
    fourRowFiniteTripleWeight (fun _ => a) = 1 := by simp [fourRowFiniteTripleWeight]

def fourRowFiniteFiveEquiv (n : ℕ) :
    (Fin 5 → FourRowFiniteCell n) ≃
      (Fin 3 → FourRowFiniteCell n) × (FourRowFiniteCell n × FourRowFiniteCell n) where
  toFun s := (fun i => s (Fin.castAdd 2 i), s 3, s 4)
  invFun q := ![q.1 0, q.1 1, q.1 2, q.2.1, q.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

def fourRowFiniteCertificateContribution {n : ℕ}
    (Q : (Fin 3 → FourRowFiniteCell n) → Matrix (FourRowFiniteCell n) (FourRowFiniteCell n) ℚ)
    (s : Fin 5 → FourRowFiniteCell n) : ℚ :=
  let q := fourRowFiniteFiveEquiv n s
  fourRowFiniteTripleWeight q.1 * Q q.1 q.2.1 q.2.2

def fourRowFiniteCertificatePolynomial {n : ℕ}
    (Q : (Fin 3 → FourRowFiniteCell n) → Matrix (FourRowFiniteCell n) (FourRowFiniteCell n) ℚ) :
    MvPolynomial (FourRowFiniteCell n) ℚ :=
  fourRowFiniteWeightedPolynomial (fourRowFiniteCertificateContribution Q)

/-- The five ordered positions split into a corrected triple and the actual ordered quadratic pair. -/
theorem fourRowFiniteCertificatePolynomial_eval {n : ℕ}
    (Q : (Fin 3 → FourRowFiniteCell n) → Matrix (FourRowFiniteCell n) (FourRowFiniteCell n) ℚ)
    (P : Board 4 n) :
    fourRowFinitePolynomialEval P (fourRowFiniteCertificatePolynomial Q) =
      ∑ m : Fin 3 → FourRowFiniteCell n, (fourRowFiniteTripleWeight m : ℝ) *
        (∏ t, P (m t).1 (m t).2) *
        quadraticValue ((Q m).map (fun q : ℚ => (q : ℝ))) (fun a => P a.1 a.2) := by
  classical
  calc
    _ = ∑ s : Fin 5 → FourRowFiniteCell n,
        (fourRowFiniteCertificateContribution Q s : ℝ) * ∏ t, P (s t).1 (s t).2 := by
      simp [fourRowFinitePolynomialEval, fourRowFiniteCertificatePolynomial,
        fourRowFiniteWeightedPolynomial, fourRowFiniteSampleMonomial]
    _ = ∑ q : (Fin 3 → FourRowFiniteCell n) × (FourRowFiniteCell n × FourRowFiniteCell n),
        (fourRowFiniteTripleWeight q.1 : ℝ) * (∏ t, P (q.1 t).1 (q.1 t).2) *
          (P q.2.1.1 q.2.1.2 * (Q q.1 q.2.1 q.2.2 : ℝ) * P q.2.2.1 q.2.2.2) := by
      apply Fintype.sum_equiv (fourRowFiniteFiveEquiv n)
      intro s
      simp only [fourRowFiniteCertificateContribution, fourRowFiniteFiveEquiv,
        Equiv.coe_fn_mk, Rat.cast_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
      ring_nf
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro m _
      rw [Fintype.sum_prod_type]
      simp only [quadraticValue, Finset.mul_sum, Matrix.map_apply]

theorem fourRowFiniteCertificatePolynomial_nonneg {n : ℕ}
    (Q : (Fin 3 → FourRowFiniteCell n) → Matrix (FourRowFiniteCell n) (FourRowFiniteCell n) ℚ)
    (hQ : ∀ m, ((Q m).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (P : Board 4 n) (hP : ∀ i j, 0 ≤ P i j) :
    0 ≤ fourRowFinitePolynomialEval P (fourRowFiniteCertificatePolynomial Q) := by
  rw [fourRowFiniteCertificatePolynomial_eval]
  apply Finset.sum_nonneg
  intro m _
  apply mul_nonneg
  · exact mul_nonneg (Rat.cast_nonneg.mpr (fourRowFiniteTripleWeight_pos m).le)
      (Finset.prod_nonneg fun t _ => hP _ _)
  · simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      (hQ m).dotProduct_mulVec_nonneg (fun a => P a.1 a.2)

/-- Strictness uses one repeated positive cell and therefore keeps every simplex boundary. -/
theorem fourRowFiniteCertificatePolynomial_zero_iff {n : ℕ}
    (Q : (Fin 3 → FourRowFiniteCell n) → Matrix (FourRowFiniteCell n) (FourRowFiniteCell n) ℚ)
    (hQ : ∀ m, ((Q m).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hkernel : ∀ m, ∀ x : FourRowFiniteCell n → ℝ,
      quadraticValue ((Q m).map (fun q : ℚ => (q : ℝ))) x = 0 ↔ ∃ c, ∀ a, x a = c)
    (P : Board 4 n) (hP : IsProbability P) :
    fourRowFinitePolynomialEval P (fourRowFiniteCertificatePolynomial Q) = 0 ↔
      P = uniformBoard 4 n := by
  classical
  have hquad (m : Fin 3 → FourRowFiniteCell n) :
      0 ≤ quadraticValue ((Q m).map (fun q : ℚ => (q : ℝ))) (fun a => P a.1 a.2) := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      (hQ m).dotProduct_mulVec_nonneg (fun a => P a.1 a.2)
  constructor
  · intro hz
    have hsumpos : 0 < ∑ a : FourRowFiniteCell n, P a.1 a.2 := by
      rw [sum_cell_weights, hP.2]
      norm_num
    obtain ⟨a, _, ha⟩ := (Finset.sum_pos_iff_of_nonneg (fun a _ => hP.1 a.1 a.2)).mp hsumpos
    let m : Fin 3 → FourRowFiniteCell n := fun _ => a
    have hweight : 0 < (fourRowFiniteTripleWeight m : ℝ) * ∏ t, P (m t).1 (m t).2 := by
      apply mul_pos
      · exact Rat.cast_pos.mpr (fourRowFiniteTripleWeight_pos m)
      · exact Finset.prod_pos fun _ _ => ha
    rw [fourRowFiniteCertificatePolynomial_eval] at hz
    have hterm (t : Fin 3 → FourRowFiniteCell n) :
        0 ≤ (fourRowFiniteTripleWeight t : ℝ) * (∏ i, P (t i).1 (t i).2) *
          quadraticValue ((Q t).map (fun q : ℚ => (q : ℝ))) (fun b => P b.1 b.2) :=
      mul_nonneg
        (mul_nonneg (Rat.cast_nonneg.mpr (fourRowFiniteTripleWeight_pos t).le)
          (Finset.prod_nonneg fun i _ => hP.1 (t i).1 (t i).2)) (hquad t)
    have hle := Finset.single_le_sum (s := Finset.univ) (fun t _ => hterm t) (Finset.mem_univ m)
    rw [hz] at hle
    have hzero : quadraticValue ((Q m).map (fun q : ℚ => (q : ℝ))) (fun b => P b.1 b.2) = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right hle hweight) (hquad m)
    obtain ⟨c, hc⟩ := (hkernel m _).mp hzero
    have hn : 0 < n := Nat.zero_lt_of_lt a.2.isLt
    apply eq_uniformBoard_of_equal_rows_columns (by norm_num) hn hP
    · intro i j k
      exact (hc (i,j)).trans (hc (i,k)).symm
    · intro i j k
      exact (hc (i,k)).trans (hc (j,k)).symm
  · rintro rfl
    rw [fourRowFiniteCertificatePolynomial_eval]
    apply Finset.sum_eq_zero
    intro m _
    have hz := (hkernel m (fun a => uniformBoard 4 n a.1 a.2)).mpr
      ⟨((4 : ℝ)*n)⁻¹, fun _ => rfl⟩
    rw [hz, mul_zero]

end
end DittertRybin
