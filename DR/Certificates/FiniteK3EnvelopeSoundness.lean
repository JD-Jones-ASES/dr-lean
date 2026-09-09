import DR.Certificates.FiniteK3EnvelopeCertificate
import DR.Certificates.FiniteK3Physical
import DR.Certificates.FiniteK3Pairs
import DR.Certificates.FiniteK3Soundness

/-! Soundness of the finite envelope's complete certificate interface. The
33 rational equations, four aggregate kernels and eight strict small blocks
are transferred to the actual iid inequality and its exact equality case. -/

namespace DittertRybin.Certificates
open scoped BigOperators

theorem FiniteK3EnvelopeValid.coefficientEquations {m n : ℕ} {hm : 2 ≤ m}
    {coeff : Fin 93 → ℚ} (h : FiniteK3EnvelopeValid m n hm coeff) :
    FiniteK3CoefficientEquations (uniformSeparationValue m n 3) (fun i => (coeff i : ℝ)) := by
  intro a
  have ha := congrArg (fun q : ℚ => (q : ℝ)) (h.1 a)
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast,
    finiteK3EnvelopeAlpha_cast] using ha

theorem FiniteK3EnvelopeValid.representative {m n : ℕ} {hm : 2 ≤ m}
    {coeff : Fin 93 → ℚ} (h : FiniteK3EnvelopeValid m n hm coeff) (hn : 4 ≤ n) (s : Fin 4) :
    let hkn : finiteK3DistinguishedColumns s < n := by
      have := finiteK3DistinguishedColumns_le_two s
      omega
    Matrix.PosSemidef (finiteK3Entry (fun i => (coeff i : ℝ))
      ((finiteK3FirstCell m hm s).1,(finiteK3FirstCell m hm s).2.castLE hkn.le)
      ((finiteK3SecondCell m hm s).1,(finiteK3SecondCell m hm s).2.castLE hkn.le)) ∧
    ∀ p : Fin m × Fin n → ℝ,
      quadraticValue (finiteK3Entry (fun i => (coeff i : ℝ))
        ((finiteK3FirstCell m hm s).1,(finiteK3FirstCell m hm s).2.castLE hkn.le)
        ((finiteK3SecondCell m hm s).1,(finiteK3SecondCell m hm s).2.castLE hkn.le)) p = 0 ↔
          ∃ t : ℝ, ∀ a, p a = t := by
  dsimp only
  apply finiteK3Ordinary_rational_rectangle_criterion (by omega)
    (by have := finiteK3DistinguishedColumns_le_two s; omega)
  · intro i
    simpa only [finiteK3OrdinaryBFlat, finiteK3AggregateKernelFlat_apply,
      finiteK3EnvelopeFlatB, finiteK3EnvelopeB, finiteK3EnvelopeKernel] using (h.2 s).2.2 i
  · exact (h.2 s).2.1
  · exact (h.2 s).1

/-- A valid rational catalogue entry is a theorem on the entire probability simplex. -/
theorem FiniteK3EnvelopeValid.uniformMaximizer {m n : ℕ} {hm : 2 ≤ m}
    {coeff : Fin 93 → ℚ} (h : FiniteK3EnvelopeValid m n hm coeff) (hn : 4 ≤ n) :
    UniformMaximizer m n 3 := by
  let r0 : Fin m := ⟨0, by omega⟩
  let r1 : Fin m := ⟨1, by omega⟩
  let c0 : Fin n := ⟨0, by omega⟩
  let c1 : Fin n := ⟨1, by omega⟩
  have hr : r0 ≠ r1 := by
    intro heq
    exact Nat.zero_ne_one (congrArg Fin.val heq)
  have hc : c0 ≠ c1 := by
    intro heq
    exact Nat.zero_ne_one (congrArg Fin.val heq)
  have hrep (s : Fin 4) :
      Matrix.PosSemidef (finiteK3Entry (fun i => (coeff i : ℝ)) (r0,c0)
        (finiteK3CanonicalSecond r0 r1 c0 c1 s)) ∧
      ∀ p : Fin m × Fin n → ℝ,
        quadraticValue (finiteK3Entry (fun i => (coeff i : ℝ)) (r0,c0)
          (finiteK3CanonicalSecond r0 r1 c0 c1 s)) p = 0 ↔
          ∃ t : ℝ, ∀ a, p a = t := by
    have hs := h.representative hn s
    dsimp only at hs
    have hkn : finiteK3DistinguishedColumns s < n := by
      have := finiteK3DistinguishedColumns_le_two s
      omega
    have hf : ((finiteK3FirstCell m hm s).1,
        (finiteK3FirstCell m hm s).2.castLE hkn.le) = (r0,c0) := by
      apply Prod.ext <;> apply Fin.ext <;> rfl
    have hg : ((finiteK3SecondCell m hm s).1,
        (finiteK3SecondCell m hm s).2.castLE hkn.le) = finiteK3CanonicalSecond r0 r1 c0 c1 s := by
      fin_cases s <;> apply Prod.ext <;> apply Fin.ext <;> rfl
    rw [hf,hg] at hs
    exact hs
  have hall := finiteK3_allPairs_of_fourRepresentatives (fun i => (coeff i : ℝ))
    r0 r1 c0 c1 hr hc hrep
  apply finiteK3_uniformMaximizer (by omega) (by omega) (fun i => (coeff i : ℝ))
    h.coefficientEquations (fun e f => (hall e f).1)
  intro e p hp
  exact ((hall e e).2 p).mp hp

end DittertRybin.Certificates
