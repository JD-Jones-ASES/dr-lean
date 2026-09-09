import DR.Certificates.FiniteK3EnvelopeIntegerEquations
import DR.Certificates.FiniteK3QuarticSparseData

/-! The literal33 rational equations have only93 nonzero integer coefficients.
The sparse check is formally transferred to their full93-column definition. -/
namespace DittertRybin.Certificates
open scoped BigOperators

def finiteK3QuarticSparseWeight (a : Fin 33) (t : Fin 6) : Nat :=
  ((finiteK3QuarticSparseTerms.get a).get t).1

def finiteK3QuarticSparseIndex (a : Fin 33) (t : Fin 6) : Fin 93 :=
  ((finiteK3QuarticSparseTerms.get a).get t).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem finiteK3QuarticSparse_checked : ∀ (a : Fin 33) (k : Fin 93),
    (finiteK3QuarticRows.get a).get k =
      ∑ t,if finiteK3QuarticSparseIndex a t=k then finiteK3QuarticSparseWeight a t else 0 := by
  decide +kernel

theorem finiteK3QuarticSparse_sum (a : Fin 33) (c : Fin 93 → ℤ) :
    (∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℤ)*c k)=
      ∑ t,(finiteK3QuarticSparseWeight a t:ℤ)*c (finiteK3QuarticSparseIndex a t) := by
  simp only [finiteK3QuarticSparse_checked,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,
    Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]

def FiniteK3EnvelopeSparseIntegerEquations (D : Nat) (A : ℤ) (c : Fin 93 → ℤ) : Prop :=
  ∀ a : Fin 33,(∑ t,(finiteK3QuarticSparseWeight a t:ℤ)*c (finiteK3QuarticSparseIndex a t))=
    (finiteK3QuarticMultiplicity.get a:ℤ)*A-(finiteK3QuarticSuccesses.get a:ℤ)*D

instance (D : Nat) (A : ℤ) (c : Fin 93 → ℤ) :
    Decidable (FiniteK3EnvelopeSparseIntegerEquations D A c) := by
  unfold FiniteK3EnvelopeSparseIntegerEquations
  infer_instance

theorem finiteK3EnvelopeIntegerEquations_of_sparse (D : Nat) (A : ℤ) (c : Fin 93 → ℤ)
    (h : FiniteK3EnvelopeSparseIntegerEquations D A c) : FiniteK3EnvelopeIntegerEquations D A c := by
  intro a
  rw [finiteK3QuarticSparse_sum]
  exact h a

end DittertRybin.Certificates
