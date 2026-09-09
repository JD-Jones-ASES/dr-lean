import DR.Certificates.FiniteK3QuarticProbability
import DR.Maximizers

/-! Soundness of finite K=3 certificates on the entire probability simplex.
The quartic equations give the actual objective. Positive semidefinite pair
matrices give the inequality; an exact constant kernel for diagonal pairs
suffices for strict uniform equality, including every zero-entry boundary. -/
namespace DittertRybin.Certificates
open scoped BigOperators

/-- A positive diagonal multiplier detects the exact constant quadratic kernel. -/
theorem weightedPair_zero_forces_constant {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a,p a = 1)
    (Q : α → α → Matrix α α ℝ)
    (hQ : ∀ a b, (Q a b).PosSemidef)
    (hkernel : ∀ a, quadraticValue (Q a a) p = 0 → ∃ t : ℝ, ∀ b,p b=t)
    (hzero : (∑ a,∑ b,unorderedPairWeight a b*p a*p b*quadraticValue (Q a b) p)=0) :
    ∃ t : ℝ, ∀ a,p a=t := by
  have hq (a b : α) : 0 ≤ quadraticValue (Q a b) p := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      (hQ a b).dotProduct_mulVec_nonneg p
  have ht (a b : α) : 0 ≤ unorderedPairWeight a b*p a*p b*quadraticValue (Q a b) p :=
    mul_nonneg (mul_nonneg (mul_nonneg (unorderedPairWeight_nonneg a b) (hp a)) (hp b)) (hq a b)
  have hex : ∃ a,0<p a := by
    by_contra h
    push Not at h
    have hs : (∑ a,p a) ≤ 0 := Finset.sum_nonpos fun a _ => h a
    linarith
  obtain ⟨a,ha⟩ := hex
  have hterm : unorderedPairWeight a a*p a*p a*quadraticValue (Q a a) p ≤ 0 := by
    apply le_trans (Finset.single_le_sum (fun b _ => ht a b) (Finset.mem_univ a))
    have h : (∑ b,unorderedPairWeight a b*p a*p b*quadraticValue (Q a b) p) ≤
        ∑ a,∑ b,unorderedPairWeight a b*p a*p b*quadraticValue (Q a b) p :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => ht a b) (Finset.mem_univ a)
    rwa [hzero] at h
  simp only [unorderedPairWeight,if_true,one_mul] at hterm
  have hle : quadraticValue (Q a a) p ≤ 0 := by
    by_contra h
    have hh := mul_pos (mul_pos ha ha) (lt_of_not_ge h)
    linarith
  exact hkernel a (le_antisymm hle (hq a a))

/-- Every checked literal certificate supplies both the inequality and its exact equality case. -/
theorem finiteK3_uniformMaximizer {m n : ℕ} (hm : 0<m) (hn : 0<n)
    (coeff : Fin 93 → ℝ)
    (hid : FiniteK3CoefficientEquations (uniformSeparationValue m n 3) coeff)
    (hQ : ∀ e f : Fin m × Fin n, Matrix.PosSemidef (finiteK3Entry coeff e f))
    (hkernel : ∀ e : Fin m × Fin n, ∀ p : Fin m × Fin n → ℝ,
      quadraticValue (finiteK3Entry coeff e e) p = 0 → ∃ t : ℝ, ∀ a,p a=t) :
    UniformMaximizer m n 3 := by
  intro P hP
  have hidentity := finiteK3_quartic_probability_identity hid P
  rw [hP.2,one_pow,mul_one,one_mul] at hidentity
  have hq (e f : Fin m × Fin n) :
      0 ≤ quadraticValue (finiteK3Entry coeff e f) (fun a => P a.1 a.2) := by
    simpa only [quadraticValue, dotProduct, Matrix.mulVec, Finset.mul_sum, ←mul_assoc, star_trivial] using
      (hQ e f).dotProduct_mulVec_nonneg (fun a => P a.1 a.2)
  have hsum : 0 ≤ ∑ e : Fin m × Fin n, ∑ f : Fin m × Fin n,
      unorderedPairWeight e f*P e.1 e.2*P f.1 f.2*
        quadraticValue (finiteK3Entry coeff e f) (fun a => P a.1 a.2) :=
    Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun f _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (unorderedPairWeight_nonneg e f)
        (hP.1 e.1 e.2)) (hP.1 f.1 f.2)) (hq e f)
  refine ⟨by linarith only [hidentity,hsum],?_⟩
  constructor
  · intro heq
    have hz : (∑ e : Fin m × Fin n, ∑ f : Fin m × Fin n,
        unorderedPairWeight e f*P e.1 e.2*P f.1 f.2*
          quadraticValue (finiteK3Entry coeff e f) (fun a => P a.1 a.2))=0 := by
      rw [←hidentity,heq,sub_self]
    obtain ⟨t,ht⟩ := weightedPair_zero_forces_constant (fun a : Fin m × Fin n => P a.1 a.2)
      (fun a => hP.1 a.1 a.2) ((sum_cell_weights P).trans hP.2)
      (finiteK3Entry coeff) hQ (fun e => hkernel e _) hz
    apply eq_uniformBoard_of_equal_rows_columns hm hn hP
    · intro i a b
      exact (ht (i,a)).trans (ht (i,b)).symm
    · intro i j a
      exact (ht (i,a)).trans (ht (j,a)).symm
  · intro heq
    rw [heq,separationProbability_uniform hm hn]

end DittertRybin.Certificates
