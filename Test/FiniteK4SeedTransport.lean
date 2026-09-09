import DR.Certificates.FiniteK4SeedTransport

namespace DittertRybin.Tests
open Certificates

-- Signed coefficients and literal repeated multiplier cells are preserved.
example (coeff : Fin 407 → ℝ) (e f : Fin 4 × Fin 5) :
    finiteK4Entry coeff (![e,e,f] ∘ Equiv.swap 0 2) = finiteK4Entry coeff ![e,e,f] :=
  finiteK4Entry_multiplier_perm coeff _ _

-- The full physical matrix is symmetric before any positivity assumption.
example (coeff : Fin 407 → ℝ) (t : Fin 3 → Fin 5 × Fin 20) :
    (finiteK4Entry coeff t).IsSymm := finiteK4Entry_isSymm coeff t

-- Actual host conjugacy works with no spare row or column for a diagonal seed.
example (coeff : Fin 407 → ℝ) (ρ κ : Equiv.Perm (Fin 3)) :
    (finiteK4Entry coeff (Equiv.prodCongr ρ κ ∘ finiteTripleSeed 9)).submatrix
      (Equiv.prodCongr ρ κ) (Equiv.prodCongr ρ κ) = finiteK4Entry coeff (finiteTripleSeed 9) :=
  finiteK4Entry_physical coeff _ ρ κ

-- A literal negative coefficient yields a negative singleton quadratic form;
-- coverage alone is never a positivity proof.
example : quadraticValue (finiteK4Entry (fun _ => -1) (fun _ => (0,0) : Fin 3 → Fin 1 × Fin 1))
    (fun _ => 1) = -1 := by
  norm_num [quadraticValue,finiteK4Entry]

#print axioms finiteK4Entry_isSymm
#print axioms finiteK4Entry_multiplier_perm
#print axioms finiteK4Entry_physical
#print axioms finiteK4Entry_seed_submatrix
#print axioms finiteK4Entry_criterion_of_seeds
end DittertRybin.Tests
