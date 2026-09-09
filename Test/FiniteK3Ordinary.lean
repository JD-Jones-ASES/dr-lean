import DR.Certificates.FiniteK3Ordinary

open scoped BigOperators
open DittertRybin.Certificates

-- Distinguished cells are row-major; the aggregate rows occupy the final positions.
example : finiteK3AggregateEquiv 2 2 (.inl (1,0)) = 2 := rfl
example : finiteK3AggregateEquiv 2 2 (.inr 1) = 5 := rfl

-- The aggregate ordinary coordinates represent sums of ell individual columns.
example : finiteK3AggregateKernelFlat 2 2 (3 : ℚ) = ![1,1,1,1,3,3] := by decide +kernel
example : finiteK3AggregateKernelFlat 2 1 (7 : ℚ) = ![1,1,7,7] := by decide +kernel

-- Casting exact rational block data preserves the actual division by ell.
example (coeff : Fin 93 → ℚ) (e f : Fin 3 × Fin 2) (ell : ℚ) :
    (finiteK3OrdinaryB coeff e f ell).map (fun q : ℚ => (q : ℝ)) =
      finiteK3OrdinaryB (fun i => (coeff i : ℝ)) e f (ell : ℝ) :=
  finiteK3OrdinaryB_cast coeff e f ell

-- With no ordinary columns the physical matrix consists of its distinguished block.
example (coeff : Fin 93 → ℝ) (e f a b : Fin 2 × Fin 2) :
    finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
      (a.1,Sum.inl a.2) ((b.1,Sum.inl b.2) : Fin 2 × (Fin 2 ⊕ Fin 0)) =
      finiteK3OrdinaryA coeff e f a b := finiteK3Ordinary_left_left coeff e f a b
example : ¬((Fintype.card (Fin 0) : ℝ) ≠ 0) := by norm_num

#print axioms finiteK3Entry_ordinaryColumnMatrix
#print axioms finiteK3OrdinaryO_isSymm
#print axioms finiteK3OrdinaryH_cast
#print axioms finiteK3OrdinaryB_cast
