import DR.Certificates.Gram
import DR.Certificates.QuarticSampling

/-! Ordered-triple correction and signed evaluation of quintic quadratic
certificates. All three repetition cases and empty outcome types are retained. -/
namespace DittertRybin.Certificates
open scoped BigOperators

noncomputable def unorderedTripleWeight {α : Type*} [DecidableEq α] (m : Fin 3 → α) : ℝ :=
  if m 0 = m 1 ∧ m 1 = m 2 then 1
  else if m 0 = m 1 ∨ m 0 = m 2 ∨ m 1 = m 2 then 1/3 else 1/6

theorem unorderedTripleWeight_pos {α : Type*} [DecidableEq α] (m : Fin 3 → α) :
    0 < unorderedTripleWeight m := by
  unfold unorderedTripleWeight
  split_ifs <;> norm_num

theorem unorderedTripleWeight_repeat {α : Type*} [DecidableEq α] (a : α) :
    unorderedTripleWeight (fun _ => a) = 1 := by
  simp [unorderedTripleWeight]

def sampleFiveTripleEquiv (α : Type*) :
    (Fin 5 → α) ≃ (Fin 3 → α) × (α × α) where
  toFun s := (fun i => s (Fin.castAdd 2 i), s 3, s 4)
  invFun q := ![q.1 0, q.1 1, q.1 2, q.2.1, q.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl

/-- Reindexing into a multiplier triple and two quadratic coordinates is exact on signed inputs. -/
theorem sum_sample_five_weighted_quadratic {α : Type*} [Fintype α]
    (p : α → ℝ) (w : (Fin 3 → α) → ℝ) (Q : (Fin 3 → α) → Matrix α α ℝ) :
    (∑ s : Fin 5 → α, sampleMass p s * w (fun i => s (Fin.castAdd 2 i)) *
      Q (fun i => s (Fin.castAdd 2 i)) (s 3) (s 4)) =
      ∑ m : Fin 3 → α, w m * (∏ t, p (m t)) * quadraticValue (Q m) p := by
  classical
  calc
    _ = ∑ q : (Fin 3 → α) × (α × α), w q.1 * (∏ t, p (q.1 t)) *
        (p q.2.1 * Q q.1 q.2.1 q.2.2 * p q.2.2) := by
      apply Fintype.sum_equiv (sampleFiveTripleEquiv α)
      intro s
      simp only [sampleFiveTripleEquiv, Equiv.coe_fn_mk, sampleMass,
        Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
      change (p (s 0) * (p (s 1) * (p (s 2) * (p (s 3) * p (s 4))))) *
          w (fun i => s (Fin.castAdd 2 i)) *
          Q (fun i => s (Fin.castAdd 2 i)) (s 3) (s 4) =
        w (fun i => s (Fin.castAdd 2 i)) * (p (s 0) * (p (s 1) * p (s 2))) *
          (p (s 3) * Q (fun i => s (Fin.castAdd 2 i)) (s 3) (s 4) * p (s 4))
      ring
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro m _
      rw [Fintype.sum_prod_type]
      simp only [quadraticValue, Finset.mul_sum]

/-- One repeated positive cell detects a constant kernel, even on a boundary support. -/
theorem weightedTriple_zero_forces_constant {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1)
    (Q : (Fin 3 → α) → Matrix α α ℝ)
    (hQ : ∀ m, (Q m).PosSemidef)
    (hkernel : ∀ a, quadraticValue (Q (fun _ => a)) p = 0 → ∃ t : ℝ, ∀ b, p b = t)
    (hzero : (∑ m : Fin 3 → α, unorderedTripleWeight m * (∏ t, p (m t)) *
      quadraticValue (Q m) p) = 0) :
    ∃ t : ℝ, ∀ a, p a = t := by
  have hq (m : Fin 3 → α) : 0 ≤ quadraticValue (Q m) p := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      (hQ m).dotProduct_mulVec_nonneg p
  have ht (m : Fin 3 → α) : 0 ≤ unorderedTripleWeight m * (∏ t, p (m t)) *
      quadraticValue (Q m) p :=
    mul_nonneg (mul_nonneg (unorderedTripleWeight_pos m).le
      (Finset.prod_nonneg fun t _ => hp (m t))) (hq m)
  have hsumpos : 0 < ∑ a, p a := by rw [hmass]; norm_num
  obtain ⟨a, _, ha⟩ := (Finset.sum_pos_iff_of_nonneg (fun a _ => hp a)).mp hsumpos
  have hweight : 0 < unorderedTripleWeight (fun _ : Fin 3 => a) *
      (∏ t : Fin 3, p ((fun _ => a) t)) :=
    mul_pos (unorderedTripleWeight_pos _) (Finset.prod_pos fun _ _ => ha)
  have hterm := Finset.single_le_sum (s := Finset.univ) (fun m _ => ht m)
    (Finset.mem_univ (fun _ : Fin 3 => a))
  rw [hzero] at hterm
  exact hkernel a (le_antisymm (nonpos_of_mul_nonpos_right hterm hweight) (hq _))

end DittertRybin.Certificates
