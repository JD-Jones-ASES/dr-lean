import DR.Certificates.ConstantKernel

/-! Four actual multiplier representatives cover every pair by independent
row and column permutations. No row/column transposition is imposed. -/

namespace DittertRybin.Certificates

def finiteK3MultiplierPairType {ρ δ : Type*} [DecidableEq ρ] [DecidableEq δ]
    (e f : ρ × δ) : Fin 4 :=
  if e.1 = f.1 then (if e.2 = f.2 then 0 else 1) else (if e.2 = f.2 then 2 else 3)

def finiteK3CanonicalSecond {ρ δ : Type*} (r0 r1 : ρ) (c0 c1 : δ) (s : Fin 4) : ρ × δ :=
  (if s.val / 2 = 0 then r0 else r1, if s.val % 2 = 0 then c0 else c1)

/-- The four representative checks give positivity and the exact constant
quadratic kernel for every actual multiplier pair. -/
theorem finiteK3_allPairs_of_fourRepresentatives {ρ δ : Type*}
    [Fintype ρ] [Fintype δ] [DecidableEq ρ] [DecidableEq δ]
    (coeff : Fin 93 → ℝ) (r0 r1 : ρ) (c0 c1 : δ) (hr : r0 ≠ r1) (hc : c0 ≠ c1)
    (hrep : ∀ s : Fin 4,
      Matrix.PosSemidef (finiteK3Entry coeff (r0,c0) (finiteK3CanonicalSecond r0 r1 c0 c1 s)) ∧
      ∀ p : ρ × δ → ℝ,
        quadraticValue (finiteK3Entry coeff (r0,c0) (finiteK3CanonicalSecond r0 r1 c0 c1 s)) p = 0 ↔
          ∃ t : ℝ, ∀ a, p a = t) (e f : ρ × δ) :
    Matrix.PosSemidef (finiteK3Entry coeff e f) ∧
      ∀ p : ρ × δ → ℝ, quadraticValue (finiteK3Entry coeff e f) p = 0 ↔
        ∃ t : ℝ, ∀ a, p a = t := by
  let r := pairNormalization r0 r1 e.1 f.1
  let c := pairNormalization c0 c1 e.2 f.2
  let E := Equiv.prodCongr r c
  have he : E e = (r0,c0) := by
    simp only [E, Equiv.prodCongr_apply, Prod.map_apply', r, c,
      pairNormalization_first r0 r1 _ _ hr, pairNormalization_first c0 c1 _ _ hc]
  have hf : E f = finiteK3CanonicalSecond r0 r1 c0 c1 (finiteK3MultiplierPairType e f) := by
    by_cases hrow : e.1 = f.1 <;> by_cases hcol : e.2 = f.2 <;>
      simp [E, r, c, pairNormalization_second, finiteK3CanonicalSecond,
        finiteK3MultiplierPairType, hrow, hcol, Prod.map_apply']
  have hei : (r.symm r0,c.symm c0) = e := by
    have h := congrArg E.symm he
    simpa only [Equiv.symm_apply_apply, E, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Prod.map_apply'] using h.symm
  have hfi :
      (r.symm (finiteK3CanonicalSecond r0 r1 c0 c1 (finiteK3MultiplierPairType e f)).1,
       c.symm (finiteK3CanonicalSecond r0 r1 c0 c1 (finiteK3MultiplierPairType e f)).2) = f := by
    have h := congrArg E.symm hf
    simpa only [Equiv.symm_apply_apply, E, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Prod.map_apply'] using h.symm
  have h := finiteK3Entry_criterion_equiv coeff r.symm c.symm (r0,c0)
    (finiteK3CanonicalSecond r0 r1 c0 c1 (finiteK3MultiplierPairType e f))
    (hrep _).1 (hrep _).2
  rw [hei,hfi] at h
  exact h

end DittertRybin.Certificates
