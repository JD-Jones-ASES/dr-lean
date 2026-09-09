import DR.Certificates.FiniteTripleSeeds
import DR.Certificates.FiniteK4QuinticSampling
import DR.Certificates.ConstantKernel
import Mathlib.Data.List.FinRange

/-! Actual matrix transport from the ten multiplier seeds. The finite host
permutations conjugate the full physical matrix, and the multiplier positions
may be permuted even when their cells coincide. -/
namespace DittertRybin.Certificates
noncomputable section

theorem finiteK4Entry_roleKey {m n : ℕ} (t : Fin 3 → Fin m × Fin n)
    (a b : Fin m × Fin n) :
    finiteK4RoleKeys.get (finiteK4RoleIndex
      ![((t 0).1.val,(t 0).2.val),((t 1).1.val,(t 1).2.val),
        ((t 2).1.val,(t 2).2.val),(a.1.val,a.2.val),(b.1.val,b.2.val)]) =
      fourRowFiniteCanonicalRoleKey
        (List.ofFn (fun i => ((t i).1.val,(t i).2.val)))
        (a.1.val,a.2.val) (b.1.val,b.2.val) := by
  rw [←finiteK4RoleIndex_spec]
  simp [finiteK4TupleRoleKey,List.ofFn_succ]

theorem finiteK4Entry_isSymm {m n : ℕ} (coeff : Fin 407 → ℝ)
    (t : Fin 3 → Fin m × Fin n) : (finiteK4Entry coeff t).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  apply congrArg coeff
  apply finiteK4RoleKeys_injective
  rw [finiteK4Entry_roleKey,finiteK4Entry_roleKey]
  exact fourRowFiniteCanonicalRoleKey_swap _ _ _

theorem finiteK4Entry_multiplier_perm {m n : ℕ} (coeff : Fin 407 → ℝ)
    (t : Fin 3 → Fin m × Fin n) (σ : Equiv.Perm (Fin 3)) :
    finiteK4Entry coeff (t ∘ σ) = finiteK4Entry coeff t := by
  funext a b
  apply congrArg coeff
  apply finiteK4RoleKeys_injective
  rw [finiteK4Entry_roleKey,finiteK4Entry_roleKey]
  apply fourRowFiniteCanonicalRoleKey_perm
  exact σ.ofFn_comp_perm (fun i => ((t i).1.val,(t i).2.val))

theorem finiteK4Entry_physical {m n : ℕ} (coeff : Fin 407 → ℝ)
    (t : Fin 3 → Fin m × Fin n) (ρ : Equiv.Perm (Fin m)) (κ : Equiv.Perm (Fin n)) :
    (finiteK4Entry coeff (Equiv.prodCongr ρ κ ∘ t)).submatrix
      (Equiv.prodCongr ρ κ) (Equiv.prodCongr ρ κ) = finiteK4Entry coeff t := by
  funext a b
  apply congrArg coeff
  apply finiteK4RoleKeys_injective
  rw [finiteK4Entry_roleKey,finiteK4Entry_roleKey]
  have hnat (e : Fin m × Fin n) :
      ((ρ e.1).val,(κ e.2).val) =
        Prod.map (fourRowFiniteExtendLabel ρ) (fourRowFiniteExtendLabel κ) (e.1.val,e.2.val) := by
    simp [fourRowFiniteExtendLabel,e.1.isLt,e.2.isLt]
  change fourRowFiniteCanonicalRoleKey
    (List.ofFn (fun i => ((ρ (t i).1).val,(κ (t i).2).val)))
      ((ρ a.1).val,(κ a.2).val) ((ρ b.1).val,(κ b.2).val) = _
  simp_rw [hnat]
  simpa only [List.map_ofFn,Function.comp_def] using
    fourRowFiniteCanonicalRoleKey_map _ _ (fourRowFiniteExtendLabel_injective ρ)
      (fourRowFiniteExtendLabel_injective κ)
      (List.ofFn (fun i => ((t i).1.val,(t i).2.val))) (a.1.val,a.2.val) (b.1.val,b.2.val)

/-- The finite certificate matrices cover every physical multiplier triple. -/
theorem finiteK4Entry_seed_submatrix {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (coeff : Fin 407 → ℝ) (t : Fin 3 → Fin m × Fin n) :
    ∃ a : Fin 10, ∃ e : Equiv.Perm (Fin m × Fin n),
      finiteK4Entry coeff t =
        (finiteK4Entry coeff (finiteTriplePhysicalSeed hm hn a)).submatrix e e := by
  obtain ⟨a,σ,ρ,κ,h⟩ := finiteTripleSeed_physical_coverage hm hn t
  refine ⟨a,Equiv.prodCongr ρ κ,?_⟩
  have he : Equiv.prodCongr ρ κ ∘ (t ∘ σ) = finiteTriplePhysicalSeed hm hn a := funext h
  have hp := finiteK4Entry_physical coeff (t ∘ σ) ρ κ
  rw [he,finiteK4Entry_multiplier_perm] at hp
  exact hp.symm

/-- Seed PSD and exact constant kernels transfer to every actual triple. -/
theorem finiteK4Entry_criterion_of_seeds {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (coeff : Fin 407 → ℝ)
    (hQ : ∀ a : Fin 10, Matrix.PosSemidef (finiteK4Entry coeff (finiteTriplePhysicalSeed hm hn a)))
    (hk : ∀ a : Fin 10, ∀ x : Fin m × Fin n → ℝ,
      quadraticValue (finiteK4Entry coeff (finiteTriplePhysicalSeed hm hn a)) x = 0 ↔
        ∃ c : ℝ, ∀ i, x i = c) (t : Fin 3 → Fin m × Fin n) :
    Matrix.PosSemidef (finiteK4Entry coeff t) ∧
      ∀ x : Fin m × Fin n → ℝ, quadraticValue (finiteK4Entry coeff t) x = 0 ↔
        ∃ c : ℝ, ∀ i, x i = c := by
  obtain ⟨a,e,he⟩ := finiteK4Entry_seed_submatrix hm hn coeff t
  rw [he]
  exact psd_constant_kernel_submatrix _ e (hQ a) (hk a)

end
end DittertRybin.Certificates
