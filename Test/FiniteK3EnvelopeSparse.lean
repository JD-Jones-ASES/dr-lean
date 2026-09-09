import DR.Certificates.FiniteK3EnvelopeSparseEquations

namespace DittertRybin.Certificates.Tests
open scoped BigOperators

-- Every dense coefficient row is identified, for all signed integer coefficient vectors.
example (a : Fin 33) (c : Fin 93 → ℤ) :
    (∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℤ)*c k)=
      ∑ t,(finiteK3QuarticSparseWeight a t:ℤ)*c (finiteK3QuarticSparseIndex a t) :=
  finiteK3QuarticSparse_sum a c

-- The repeated-cell quartic equation has its literal unit coefficient, not a zero padding term.
example : finiteK3QuarticSparseWeight 0 0=1 ∧ finiteK3QuarticSparseIndex 0 0=0 := by decide +kernel
example : (finiteK3QuarticRows.get 0).get 0≠0 := by decide +kernel

example (D : Nat) (A : ℤ) (c : Fin 93 → ℤ) (h : FiniteK3EnvelopeSparseIntegerEquations D A c) :
    FiniteK3EnvelopeIntegerEquations D A c := finiteK3EnvelopeIntegerEquations_of_sparse D A c h

#print axioms finiteK3QuarticSparse_checked
#print axioms finiteK3QuarticSparse_sum
#print axioms finiteK3EnvelopeIntegerEquations_of_sparse
end DittertRybin.Certificates.Tests
