import DR.Certificates.FiniteK4QuinticSampling
import DR.Maximizers

/-! Soundness of the actual quintic quadratic identity on the closed simplex.
Only repeated-cell multiplier kernels are needed for unique equality.
The local coefficient identity and literal matrix bounds remain explicit
certificate obligations; no rectangular theorem is asserted without them. -/
namespace DittertRybin.Certificates
open scoped BigOperators

theorem finiteK4_uniformMaximizer_of_local {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (coeff : Fin 407 → ℝ)
    (hid : ∀ s : Fin 5 → Fin m × Fin n, finiteK4TripleValue coeff s =
      60 * uniformSeparationValue m n 4 - 12 * (∑ a : Fin 5,
        (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)))
    (hQ : ∀ t : Fin 3 → Fin m × Fin n, Matrix.PosSemidef (finiteK4Entry coeff t))
    (hkernel : ∀ e : Fin m × Fin n, ∀ p : Fin m × Fin n → ℝ,
      quadraticValue (finiteK4Entry coeff (fun _ => e)) p = 0 → ∃ c : ℝ, ∀ a, p a = c) :
    UniformMaximizer m n 4 := by
  intro P hP
  have he := finiteK4_probability_identity_of_local _ coeff hid P
  rw [hP.2,one_pow,mul_one,one_mul] at he
  have hq (t : Fin 3 → Fin m × Fin n) :
      0 ≤ quadraticValue (finiteK4Entry coeff t) (fun e => P e.1 e.2) := by
    simpa only [quadraticValue_eq_dotProduct, star_trivial] using
      (hQ t).dotProduct_mulVec_nonneg (fun e => P e.1 e.2)
  have hsum : 0 ≤ ∑ t : Fin 3 → Fin m × Fin n,
      unorderedTripleWeight t * (∏ i, P (t i).1 (t i).2) *
        quadraticValue (finiteK4Entry coeff t) (fun e => P e.1 e.2) :=
    Finset.sum_nonneg fun t _ =>
      mul_nonneg (mul_nonneg (unorderedTripleWeight_pos t).le
        (Finset.prod_nonneg fun i _ => hP.1 (t i).1 (t i).2)) (hq t)
  refine ⟨by linarith only [he,hsum], ?_⟩
  constructor
  · intro heq
    have hz : (∑ t : Fin 3 → Fin m × Fin n,
        unorderedTripleWeight t * (∏ i, P (t i).1 (t i).2) *
          quadraticValue (finiteK4Entry coeff t) (fun e => P e.1 e.2)) = 0 := by
      rw [←he,heq,sub_self]
    obtain ⟨c,hc⟩ := weightedTriple_zero_forces_constant (fun e : Fin m × Fin n => P e.1 e.2)
      (fun e => hP.1 e.1 e.2) ((sum_cell_weights P).trans hP.2)
      (finiteK4Entry coeff) hQ (fun e => hkernel e _) hz
    apply eq_uniformBoard_of_equal_rows_columns hm hn hP
    · intro i a b
      exact (hc (i,a)).trans (hc (i,b)).symm
    · intro i j a
      exact (hc (i,a)).trans (hc (j,a)).symm
  · intro h
    rw [h,separationProbability_uniform hm hn]

end DittertRybin.Certificates
