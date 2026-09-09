import DR.Rectangular.FourRowFinitePhysicalCriterion

/-! Generic soundness of the actual seed block conditions under positive
coefficient scaling, for every physical multiplier triple. -/

namespace DittertRybin
open Certificates
noncomputable section

theorem fourRowFinite_family_entry_criterion {N : ℕ} (hN : 5 ≤ N)
    (h : ℕ → ℝ) (u : ℝ) (hu : 0 < u)
    (hk : ∀ s, (fourRowFiniteSeedFullMatrix s N h).mulVec
      (fun j => fourRowFiniteSeedWeight s N j.val) = 0)
    (hp : ∀ s, (fourRowFiniteSeedTrivialMatrix s N h).PosDef)
    (hrow : ∀ s, fourRowFiniteSeedRows s < 3 → (fourRowFiniteSeedRowMatrix s N h).PosDef)
    (hcol : ∀ s, (fourRowFiniteSeedColumnMatrix s h).PosDef)
    (hinter : ∀ s, fourRowFiniteSeedRows s < 3 → (fourRowFiniteSeedInteractionMatrix s h).PosDef)
    (t : Fin 3 → Fin 4 × Fin N) :
    (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)/u) t).PosSemidef ∧
      ∀ x : Fin 4 × Fin N → ℝ,
        quadraticValue (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)/u) t) x = 0 ↔
          ∃ c : ℝ, ∀ i, x i = c := by
  have hs (s : Fin 10) := fourRowFiniteSeedPhysical_criterion_of_blocks hN s h
    (hk s) (hp s) (hrow s) (hcol s) (hinter s)
  have hc (s : Fin 10) :
      (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)/u)
        (finiteTriplePhysicalSeed (by decide : 3 ≤ 4) (by omega : 3 ≤ N) s)).PosSemidef ∧
      ∀ x : Fin 4 × Fin N → ℝ,
        quadraticValue (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)/u)
          (finiteTriplePhysicalSeed (by decide : 3 ≤ 4) (by omega : 3 ≤ N) s)) x = 0 ↔
            ∃ c : ℝ, ∀ i, x i = c := by
    have he : finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)/u)
        (finiteTriplePhysicalSeed (by decide : 3 ≤ 4) (by omega : 3 ≤ N) s) =
        (1/u) • finiteK4Entry (fun k => h (finiteK4RoleKeys.get k))
          (finiteTriplePhysicalSeed (by decide : 3 ≤ 4) (by omega : 3 ≤ N) s) := by
      ext i j
      simp only [finiteK4Entry,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,mul_one]
    rw [he]
    exact fourRowFinite_psd_constant_kernel_smul _ (hs s).1 (hs s).2 (1/u) (one_div_pos.mpr hu)
  exact finiteK4Entry_criterion_of_seeds (by decide) (by omega) _
    (fun s => (hc s).1) (fun s => (hc s).2) t

end
end DittertRybin
