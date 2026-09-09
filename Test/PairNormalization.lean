import DR.Certificates.PairNormalization

namespace DittertRybin.Certificates.Tests

-- Arbitrary labels, without any ambient finite-type or positivity requirement.
example {α : Type*} [DecidableEq α] (z o a b : α) (hzo : z≠o) :
    pairNormalization z o a b a=z ∧ pairNormalization z o a b b=(if a=b then z else o) :=
  ⟨pairNormalization_first z o a b hzo,pairNormalization_second z o a b⟩

-- Equal labels remain equal, rather than being spuriously mapped to two representatives.
example : pairNormalization (0:ℕ) 1 17 17 17=0 := by decide +kernel
example : pairNormalization (0:ℕ) 1 17 42 17=0 ∧
    pairNormalization (0:ℕ) 1 17 42 42=1 := by decide +kernel

-- Distinct canonical representatives are necessary to keep the first image fixed.
example : pairNormalization (0:ℕ) 0 1 2 1≠0 := by decide +kernel

#print axioms pairNormalization_first
#print axioms pairNormalization_second
#print axioms quadraticValue_submatrix_equiv
end DittertRybin.Certificates.Tests
