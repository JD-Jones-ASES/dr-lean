import DR.Certificates.SpectralFourData
import Mathlib.Data.List.Permutation
import Mathlib.Data.Fin.Basic

/-!
# The order-four sextic certificate: exact matrix layer

The first four cell positions are the unordered multiplier and the last two
are the unordered quadratic pair. Rows and columns are relabeled independently
in first-occurrence order. The minimum packed key over those role permutations
specifies each entry through the exact rational coefficient catalog.

This file proves the seed matrices' kernel and quantitative PSD claims.
The degree-six polynomial identity and full multiplier-orbit coverage are
separate obligations; no Dittert or P2 maximizer theorem is assumed here.
-/

namespace DittertRybin.Certificates

open scoped BigOperators

/-- Relabel natural labels by their first occurrence, starting at zero. -/
noncomputable def firstOccurrenceLabels (xs : List ℕ) : List ℕ :=
  (xs.foldl (fun (state : List ℕ × List ℕ) (x : ℕ) =>
    if x ∈ state.1 then (state.1, state.2 ++ [state.1.idxOf x])
    else (state.1 ++ [x], state.2 ++ [state.1.length])) ([], [])).2

/-- Normalize rows and columns separately and pack fixed-length cell tuples in base sixteen. -/
noncomputable def spectralFourNormalizedKey (cells : List ℕ) : ℕ :=
  (List.zipWith (fun r c => 4 * r + c)
    (firstOccurrenceLabels (cells.map (· / 4)))
    (firstOccurrenceLabels (cells.map (· % 4)))).foldl (fun a b => 16 * a + b) 0

/-- The insertion-order enumeration used below contains exactly all role permutations. -/
theorem spectralFourRolePermutations_complete {s t : List ℕ} :
    s ∈ t.permutations' ↔ s.Perm t := List.mem_permutations'

/-- Exact documented role canonicalization: four multiplier positions and two quadratic positions. -/
noncomputable def spectralFourCanonicalRoleKey (multiplier : Vector ℕ 4) (i j : Fin 16) : ℕ :=
  (multiplier.toList.permutations'.flatMap (fun m =>
    [i.val, j.val].permutations'.map (fun q => spectralFourNormalizedKey (m ++ q)))).foldl min (16 ^ 6)

noncomputable def spectralFourEntryRole (s : Fin 33) (i j : Fin 16) : Fin 1484 :=
  ((spectralFourEntryRoles.get s).get i).get j

/-- Efficient exact reconstruction through the verified role-index table. -/
noncomputable def spectralFourTableMatrix (s : Fin 33) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun i j => spectralFourCoefficients (spectralFourEntryRole s i j)

noncomputable def spectralFourShift (s : Fin 33) : Matrix (Fin 16) (Fin 16) ℚ :=
  spectralFourTableMatrix s - (1 / 10 : ℚ) • centeringMatrix 16

noncomputable def spectralFourCertificate (s : Fin 33) : GramCertificate 15 15 :=
  ⟨fun i => (spectralFourWeights.get s).get i,
    fun i j => ((spectralFourFactors.get s).get i).get j⟩

set_option maxRecDepth 100000 in
theorem spectralFourMultipliers_bounds : ∀ (s : Fin 33) (a : Fin 4),
    (spectralFourMultipliers.get s).get a < 16 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem spectralFourCatalog_bounds : ∀ r : Fin 1484,
    r.val / 64 < spectralFourCoefficientsChunks.size ∧
    r.val % 64 < (spectralFourCoefficientsChunks[r.val / 64]!).size ∧
    r.val / 64 < spectralFourRoleKeysChunks.size ∧
    r.val % 64 < (spectralFourRoleKeysChunks[r.val / 64]!).size := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem spectralFourRoleKeys_strictMono : StrictMono spectralFourRoleKeys := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

/-- The formula-defined entry function, with no role-index-table premise. -/
noncomputable def spectralFourRoleCoefficient (key : ℕ) : ℚ :=
  ∑ r : Fin 1484, if spectralFourRoleKeys r = key then spectralFourCoefficients r else 0

theorem spectralFourRoleCoefficient_catalog (r : Fin 1484) :
    spectralFourRoleCoefficient (spectralFourRoleKeys r) = spectralFourCoefficients r := by
  unfold spectralFourRoleCoefficient
  rw [Fintype.sum_eq_single r]
  · simp
  · intro t ht
    have hne : spectralFourRoleKeys t ≠ spectralFourRoleKeys r :=
      fun h => ht (spectralFourRoleKeys_strictMono.injective h)
    simp [hne]

noncomputable def spectralFourSeedMatrix (s : Fin 33) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun i j => spectralFourRoleCoefficient
    (spectralFourCanonicalRoleKey (spectralFourMultipliers.get s) i j)











end DittertRybin.Certificates
