import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4QuinticIdentity
import DR.Rectangular.FourRowFinitePhysicalCriterion

/-! Actual fixed-board seed soundness from strict small blocks and the full
weighted kernel. Both ambient dimensions are variable; zero matrix entries
and arbitrary signed test vectors remain in the conclusion. -/
namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section

theorem finiteK4FixedWeight_pos {m n : ℕ} (hm : 4≤m) (hn : 4≤n)
    (s : Fin 10) (i : Fin (fourRowFiniteSeedFullSize s)) :
    0<(finiteK4FixedWeight m n s i : ℝ) := by
  have hr := (fourRowFiniteSeed_counts s).2.2.1
  have hc := (fourRowFiniteSeed_counts s).2.2.2.2
  have hR : (0:ℝ)<(m-fourRowFiniteSeedRows s : ℕ) := Nat.cast_pos.mpr (by omega)
  have hC : (0:ℝ)<(n-fourRowFiniteSeedColumns s : ℕ) := Nat.cast_pos.mpr (by omega)
  unfold finiteK4FixedWeight
  rcases (fourRowFiniteSeedCompressedEquiv s).symm i with ⟨p,q⟩
  cases p <;> cases q <;> simp only [finiteK4FixedAxisWeight,one_mul,mul_one]
  all_goals positivity

theorem finiteK4FixedFullMatrix_isSymm (coeff : Fin 407 → ℝ) (m n : ℕ) (s : Fin 10) :
    (finiteK4FixedFullMatrix coeff m n s).IsSymm := by
  have hs := (fourRowFiniteSeedTrivial_isSymm s (m-fourRowFiniteSeedRows s : ℕ)
    (n-fourRowFiniteSeedColumns s : ℕ) (fun key => coeff (finiteK4FixedRoleLookup key))).submatrix
      (fourRowFiniteSeedCompressedEquiv s).symm
  rw [←finiteK4FixedFullMatrix_reindex] at hs
  have he : ((finiteK4FixedFullMatrix coeff m n s).submatrix
      (fourRowFiniteSeedCompressedEquiv s) (fourRowFiniteSeedCompressedEquiv s)).submatrix
      (fourRowFiniteSeedCompressedEquiv s).symm (fourRowFiniteSeedCompressedEquiv s).symm =
      finiteK4FixedFullMatrix coeff m n s := by
    ext i j
    simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
  rwa [he] at hs

theorem finiteK4FixedFullMatrix_criterion {m n : ℕ} (hm : 4≤m) (hn : 4≤n)
    (coeff : Fin 407 → ℝ) (s : Fin 10)
    (hk : (finiteK4FixedFullMatrix coeff m n s).mulVec (finiteK4FixedWeight m n s) = 0)
    (hp : (finiteK4FixedPrincipalMatrix coeff m n s).PosDef) :
    (finiteK4FixedFullMatrix coeff m n s).PosSemidef ∧
      ∀ x : Fin (fourRowFiniteSeedFullSize s) → ℝ,
        quadraticValue (finiteK4FixedFullMatrix coeff m n s) x=0 ↔
          ∃ t : ℝ,∀ i,x i=t*finiteK4FixedWeight m n s i := by
  have hsize : 1≤fourRowFiniteSeedFullSize s := by
    unfold fourRowFiniteSeedFullSize
    exact Nat.mul_pos (by omega) (by omega)
  let e : Fin (fourRowFiniteSeedFullSize s-1+1) ≃ Fin (fourRowFiniteSeedFullSize s) :=
    finCongr (Nat.sub_add_cancel hsize)
  apply principal_kernel_criterion (finiteK4FixedFullMatrix coeff m n s)
    (finiteK4FixedFullMatrix_isSymm coeff m n s) (finiteK4FixedWeight m n s) hk e
  · exact (finiteK4FixedWeight_pos hm hn s _).ne'
  · exact hp

theorem finiteK4FixedTrivial_criterion {m n : ℕ} (hm : 4≤m) (hn : 4≤n)
    (coeff : Fin 407 → ℝ) (s : Fin 10)
    (hk : (finiteK4FixedFullMatrix coeff m n s).mulVec (finiteK4FixedWeight m n s)=0)
    (hp : (finiteK4FixedPrincipalMatrix coeff m n s).PosDef) :
    (twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s
      (fun key => coeff (finiteK4FixedRoleLookup key)))
      (m-fourRowFiniteSeedRows s : ℕ) (n-fourRowFiniteSeedColumns s : ℕ)).PosSemidef ∧
    ∀ x : (Fin (fourRowFiniteSeedRows s) ⊕ Unit) × (Fin (fourRowFiniteSeedColumns s) ⊕ Unit) → ℝ,
      quadraticValue (twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s
        (fun key => coeff (finiteK4FixedRoleLookup key)))
        (m-fourRowFiniteSeedRows s : ℕ) (n-fourRowFiniteSeedColumns s : ℕ)) x=0 ↔
          ∃ t : ℝ,∀ i,x i=t*twoAxisAggregateWeight
            (m-fourRowFiniteSeedRows s : ℕ) (n-fourRowFiniteSeedColumns s : ℕ) i := by
  obtain ⟨hQ,hker⟩ := finiteK4FixedFullMatrix_criterion hm hn coeff s hk hp
  rw [←finiteK4FixedFullMatrix_reindex]
  refine ⟨hQ.submatrix _,fun x => ?_⟩
  rw [quadraticValue_submatrix_equiv,hker]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t,fun i => ?_⟩
    simpa only [Equiv.symm_apply_apply,finiteK4FixedWeight_reindex]
      using ht (fourRowFiniteSeedCompressedEquiv s i)
  · rintro ⟨t,ht⟩
    refine ⟨t,fun i => ?_⟩
    have hi := ht ((fourRowFiniteSeedCompressedEquiv s).symm i)
    rw [←finiteK4FixedWeight_reindex,Equiv.apply_symm_apply] at hi
    exact hi

/-- The four strict small blocks and weighted kernel certify an actual physical seed. -/
theorem finiteK4FixedSeed_criterion {m n : ℕ} (hm : 5≤m) (hn : 5≤n)
    (coeff : Fin 407 → ℝ) (s : Fin 10)
    (hk : (finiteK4FixedFullMatrix coeff m n s).mulVec (finiteK4FixedWeight m n s)=0)
    (hp : (finiteK4FixedPrincipalMatrix coeff m n s).PosDef)
    (hr : (finiteK4FixedRowMatrix coeff n s).PosDef)
    (hc : (finiteK4FixedColumnMatrix coeff m s).PosDef)
    (hi : (finiteK4FixedInteractionMatrix coeff s).PosDef) :
    (finiteK4Entry coeff (finiteTriplePhysicalSeed (by omega : 3≤m) (by omega : 3≤n) s)).PosSemidef ∧
      ∀ x : Fin m × Fin n → ℝ,
        quadraticValue (finiteK4Entry coeff
          (finiteTriplePhysicalSeed (by omega : 3≤m) (by omega : 3≤n) s)) x=0 ↔
            ∃ c : ℝ,∀ i,x i=c := by
  have hnr := (fourRowFiniteSeed_counts s).2.2.1
  have hnc := (fourRowFiniteSeed_counts s).2.2.2.2
  have hR : (Fintype.card (Fin (m-fourRowFiniteSeedRows s)) : ℝ)≠0 := by
    rw [Fintype.card_fin]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hC : (Fintype.card (Fin (n-fourRowFiniteSeedColumns s)) : ℝ)≠0 := by
    rw [Fintype.card_fin]
    exact Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨hT,hTK⟩ := finiteK4FixedTrivial_criterion (by omega : 4≤m) (by omega : 4≤n) coeff s hk hp
  have hRow : (twoAxisRowStandardMatrix (fourRowFiniteSeedRelationKernel s
      (fun key => coeff (finiteK4FixedRoleLookup key)))
      (Fintype.card (Fin (n-fourRowFiniteSeedColumns s)))).PosDef := by
    rw [Fintype.card_fin,←finiteK4FixedRowMatrix_reindex]
    exact hr.submatrix (fourRowFiniteCompressedEquiv _).injective
  have hCol : (twoAxisColumnStandardMatrix (fourRowFiniteSeedRelationKernel s
      (fun key => coeff (finiteK4FixedRoleLookup key)))
      (Fintype.card (Fin (m-fourRowFiniteSeedRows s)))).PosDef := by
    rw [Fintype.card_fin,←finiteK4FixedColumnMatrix_reindex]
    exact hc.submatrix (fourRowFiniteCompressedEquiv _).injective
  have hInter : 0<twoAxisInteraction (fourRowFiniteSeedRelationKernel s
      (fun key => coeff (finiteK4FixedRoleLookup key))) := by
    rw [←finiteK4FixedInteractionMatrix_eq]
    exact hi.diag_pos (i:=(0:Fin 1))
  have hT' : (twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s
      (fun key => coeff (finiteK4FixedRoleLookup key)))
      (Fintype.card (Fin (m-fourRowFiniteSeedRows s)))
      (Fintype.card (Fin (n-fourRowFiniteSeedColumns s)))).PosSemidef := by
    simpa only [Fintype.card_fin] using hT
  have hQ := twoAxisOrdinaryMatrix_posSemidef _
    (fourRowFiniteSeedRelationKernel_symm s (fun key => coeff (finiteK4FixedRoleLookup key)))
    hR hC hT' (Or.inr hRow.posSemidef) (Or.inr hCol.posSemidef) (Or.inr (Or.inr hInter.le))
  have hK : ∀ x : (Fin (fourRowFiniteSeedRows s) ⊕ Fin (m-fourRowFiniteSeedRows s)) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Fin (n-fourRowFiniteSeedColumns s)) → ℝ,
      quadraticValue (twoAxisOrdinaryMatrix (fourRowFiniteSeedRelationKernel s
        (fun key => coeff (finiteK4FixedRoleLookup key)))) x=0 ↔ ∃ c : ℝ,∀ i,x i=c := by
    intro x
    apply twoAxisOrdinaryMatrix_constant_kernel _
      (fourRowFiniteSeedRelationKernel_symm s (fun key => coeff (finiteK4FixedRoleLookup key)))
      hR hC hT' (Or.inr hRow) (Or.inr hCol) (Or.inr (Or.inr hInter))
    simpa only [Fintype.card_fin] using hTK
  have hf := fourRowFiniteSeedMatrix_criterion (by omega : 3≤m) (by omega : 3≤n) s
    (fun key => coeff (finiteK4FixedRoleLookup key)) hQ hK
  simpa only [finiteK4FixedRoleLookup_key] using hf

/-- Literal conditions for the ten seeds imply the full closed-simplex theorem. -/
theorem finiteK4Fixed_uniformMaximizer {m n : ℕ} (hm : 5≤m) (hn : 5≤n)
    (coeff : Fin 407 → ℝ)
    (he : FiniteK4CoefficientEquations (uniformSeparationValue m n 4) coeff)
    (hk : ∀ s : Fin 10,(finiteK4FixedFullMatrix coeff m n s).mulVec (finiteK4FixedWeight m n s)=0)
    (hp : ∀ s : Fin 10,(finiteK4FixedPrincipalMatrix coeff m n s).PosDef)
    (hr : ∀ s : Fin 10,(finiteK4FixedRowMatrix coeff n s).PosDef)
    (hc : ∀ s : Fin 10,(finiteK4FixedColumnMatrix coeff m s).PosDef)
    (hi : ∀ s : Fin 10,(finiteK4FixedInteractionMatrix coeff s).PosDef) :
    UniformMaximizer m n 4 := by
  have hs (s : Fin 10) := finiteK4FixedSeed_criterion hm hn coeff s (hk s) (hp s) (hr s) (hc s) (hi s)
  have ht := finiteK4Entry_criterion_of_seeds (by omega : 3≤m) (by omega : 3≤n) coeff
    (fun s => (hs s).1) (fun s => (hs s).2)
  apply he.uniformMaximizer (by omega) (by omega) (fun t => (ht t).1)
  intro e p hzero
  exact ((ht (fun _ => e)).2 p).mp hzero

end
end DittertRybin.Certificates
