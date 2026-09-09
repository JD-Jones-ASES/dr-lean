import DR.Certificates.SpectralFour

/-!
Exact replay controls for all thirty-three formula-defined order-four seeds.
These tests certify the matrix layer; no polynomial identity is inferred here.
-/

namespace DittertRybin.Tests.SpectralFour

open scoped BigOperators
open Certificates

example : firstOccurrenceLabels [3, 1, 3, 0, 1, 0] = [0, 1, 0, 2, 1, 2] := by decide +kernel

-- Independent row and column renaming is performed in first-occurrence order.
example : spectralFourNormalizedKey [15, 13, 3, 1] = spectralFourNormalizedKey [0, 1, 4, 5] := by
  decide +kernel

-- Equal untyped six-cell multisets cannot erase the multiplier/quadratic role distinction.
example : spectralFourCanonicalRoleKey ⟨#[0, 0, 0, 0], rfl⟩ 1 1 ≠
    spectralFourCanonicalRoleKey ⟨#[0, 0, 0, 1], rfl⟩ 0 1 := by decide +kernel

-- The canonicalization does not silently identify row and column labels.
example : spectralFourCanonicalRoleKey ⟨#[0, 0, 0, 0], rfl⟩ 1 1 ≠
    spectralFourCanonicalRoleKey ⟨#[0, 0, 0, 0], rfl⟩ 4 4 := by decide +kernel

example : StrictMono spectralFourRoleKeys := spectralFourRoleKeys_strictMono

-- Every actually used role index decodes to the directly canonicalized six-cell pattern.
example : ∀ (s : Fin 33) (i j : Fin 16),
    spectralFourRoleKeys (spectralFourEntryRole s i j) =
      spectralFourCanonicalRoleKey (spectralFourMultipliers.get s) i j := spectralFourEntryRoleKey

example : ∀ s : Fin 33, (spectralFourCertificate s).Valid
    ((spectralFourShift s).submatrix Fin.castSucc Fin.castSucc) := spectralFourCertificate_valid

-- Altering a diagonal entry rejects the stored Gram factorization.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
example : ¬ (spectralFourCertificate 0).Valid
    ((spectralFourShift 0).submatrix Fin.castSucc Fin.castSucc + 1) := by decide +kernel

-- Adding identity also destroys the physical constant-vector kernel.
set_option maxRecDepth 100000 in
example : (∑ j, (spectralFourTableMatrix 0 + 1) 0 j) ≠ 0 := by decide +kernel

example (s : Fin 33) :
    ((spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ))).PosSemidef := spectralFourSeedMatrix_posSemidef s

example (s : Fin 33) : quadraticValue
    ((spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ))) (fun _ => 7) = 0 :=
  (spectralFourSeedMatrix_kernel s _).mpr ⟨7, fun _ => rfl⟩

-- A nonconstant boundary vector retains a quantitative positive quadratic value.
example (s : Fin 33) : (3 / 32 : ℝ) ≤ quadraticValue
    ((spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ)))
    (fun i => if i = 0 then 1 else 0) := by
  have h := spectralFourSeedMatrix_lower s (fun i => if i = 0 then 1 else 0)
  norm_num at h
  exact h

#print axioms DittertRybin.Certificates.spectralFourEntryRoleKey
#print axioms DittertRybin.Certificates.spectralFourCertificate_valid
#print axioms DittertRybin.Certificates.spectralFourSeedMatrix_lower
#print axioms DittertRybin.Certificates.spectralFourSeedMatrix_kernel

end DittertRybin.Tests.SpectralFour
