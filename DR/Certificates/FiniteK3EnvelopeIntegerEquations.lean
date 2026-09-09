import DR.Certificates.FiniteK3EnvelopeCertificate

/-! A common denominator turns each exact quartic gate into integer arithmetic.
The transfer theorem proves the original rational equations, rather than using
the integer check as an external claim. -/
namespace DittertRybin.Certificates
open scoped BigOperators

def FiniteK3EnvelopeIntegerEquations (D : Nat) (A : ℤ) (c : Fin 93 → ℤ) : Prop :=
  ∀ a : Fin 33,(∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℤ)*c k)=
    (finiteK3QuarticMultiplicity.get a:ℤ)*A-(finiteK3QuarticSuccesses.get a:ℤ)*D

instance (D : Nat) (A : ℤ) (c : Fin 93 → ℤ) :
    Decidable (FiniteK3EnvelopeIntegerEquations D A c) := by
  unfold FiniteK3EnvelopeIntegerEquations
  infer_instance

theorem finiteK3EnvelopeEquations_of_integer (m n D : Nat) (A : ℤ) (c : Fin 93 → ℤ)
    (hD : 0<D) (hAlpha : finiteK3EnvelopeAlpha m n=(A:ℚ)/D)
    (h : FiniteK3EnvelopeIntegerEquations D A c) :
    FiniteK3EnvelopeEquations m n (fun i => (c i:ℚ)/D) := by
  intro a
  have hD0 : (D:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have heq : (∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℚ)*(c k:ℚ))=
      (finiteK3QuarticMultiplicity.get a:ℚ)*(A:ℚ)-(finiteK3QuarticSuccesses.get a:ℚ)*D := by
    exact_mod_cast h a
  calc
    _ = (∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℚ)*(c k:ℚ))/D := by
      simp only [Finset.sum_div,mul_div_assoc]
    _ = ((finiteK3QuarticMultiplicity.get a:ℚ)*(A:ℚ)-
        (finiteK3QuarticSuccesses.get a:ℚ)*D)/D := by rw [heq]
    _ = _ := by rw [hAlpha]; field_simp

end DittertRybin.Certificates
