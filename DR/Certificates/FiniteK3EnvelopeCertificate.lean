import DR.Certificates.FiniteK3EnvelopeBlocks
import DR.Certificates.StrictGram
import DR.Certificates.FiniteK3QuarticData
import DR.Uniform

/-! Exact certificate obligations for one rectangle in the finite K3 envelope.
These are rational polynomial equations and actual small-block positivity;
no statement about the maximum of the sampling functional is assumed. -/
namespace DittertRybin.Certificates
open scoped BigOperators

def finiteK3EnvelopeAlpha (m n : Nat) : ℚ :=
  let a : ℚ := (m.descFactorial 3:ℚ)/(m:ℚ)^3
  let b : ℚ := (n.descFactorial 3:ℚ)/(n:ℚ)^3
  a+b-a*b

theorem finiteK3EnvelopeAlpha_cast (m n : Nat) :
    (finiteK3EnvelopeAlpha m n:ℝ)=uniformSeparationValue m n 3 := by
  simp only [finiteK3EnvelopeAlpha,uniformSeparationValue,distinctUniformProbability,
    Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]

def finiteK3EnvelopeB0 (coeff : Fin 93 → ℚ) (m n : Nat) (hm : 2≤m) (s : Fin 4) :=
  (finiteK3EnvelopeFlatB coeff m n hm s).submatrix
    (Fin.castLE (Nat.sub_le (m*finiteK3DistinguishedColumns s+m) 1))
    (Fin.castLE (Nat.sub_le (m*finiteK3DistinguishedColumns s+m) 1))

def finiteK3EnvelopeTableB0 (coeff : Fin 93 → ℚ) (m n : Nat) (hm9 : m≤9) (s : Fin 4) :=
  (finiteK3EnvelopeFlatTableB coeff m n hm9 s).submatrix
    (Fin.castLE (Nat.sub_le (m*finiteK3DistinguishedColumns s+m) 1))
    (Fin.castLE (Nat.sub_le (m*finiteK3DistinguishedColumns s+m) 1))

theorem finiteK3EnvelopeB0_eq_table (coeff : Fin 93 → ℚ) (m n : Nat)
    (hm : 2≤m) (hm9 : m≤9) (s : Fin 4) :
    finiteK3EnvelopeB0 coeff m n hm s=finiteK3EnvelopeTableB0 coeff m n hm9 s := by
  rw [finiteK3EnvelopeB0,finiteK3EnvelopeFlatB_eq_table]
  rfl

def FiniteK3EnvelopeEquations (m n : Nat) (coeff : Fin 93 → ℚ) : Prop :=
  ∀ a : Fin 33,(∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℚ)*coeff k)=
    (finiteK3QuarticMultiplicity.get a:ℚ)*finiteK3EnvelopeAlpha m n-
      (finiteK3QuarticSuccesses.get a:ℚ)

instance (m n : Nat) (coeff : Fin 93 → ℚ) : Decidable (FiniteK3EnvelopeEquations m n coeff) := by
  unfold FiniteK3EnvelopeEquations
  infer_instance

def FiniteK3EnvelopeValid (m n : Nat) (hm : 2≤m) (coeff : Fin 93 → ℚ) : Prop :=
  FiniteK3EnvelopeEquations m n coeff ∧ ∀ s : Fin 4,
    ((finiteK3EnvelopeH coeff m hm s).map (fun q : ℚ => (q:ℝ))).PosDef ∧
    ((finiteK3EnvelopeB0 coeff m n hm s).map (fun q : ℚ => (q:ℝ))).PosDef ∧
    ∀ i,(∑ j,finiteK3EnvelopeFlatB coeff m n hm s i j*finiteK3EnvelopeKernel m n s j)=0

end DittertRybin.Certificates
