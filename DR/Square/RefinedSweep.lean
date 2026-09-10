import DR.Square.WeightedSweep
import DR.Certificates.Gram

/-!
# The exact fourteen-vertex path and refined weighted sweep

The rational certificate reconstructs the leading 13-by-13 block of
`L_path - (1/20)(I - J/14)`. Its exact LDL factors have positive pivots;
the full shifted matrix has the constant vector in its kernel. This is
the centered form of the spectral lower bound on the zero-sum subspace.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates

/-- The ordinary path Laplacian, with endpoint degree one. -/
def pathLaplacianFourteen : Matrix (Fin 14) (Fin 14) ℚ := fun i j =>
  if i = j then (if i.val = 0 ∨ i.val = 13 then 1 else 2)
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

def pathShiftFourteen : Matrix (Fin 14) (Fin 14) ℚ :=
  pathLaplacianFourteen - (1 / 20 : ℚ) • centeringMatrix 14

/-- Exact rational LDL data, independently reconstructed from the matrix above. -/
def pathShiftLower : Matrix (Fin 13) (Fin 13) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-93 / 89), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (1 / 267), (-1767 / 1624), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (1 / 267), (13 / 1624), (-96319 / 85109), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (-1674061 / 1420990), 1, 0, 0, 0, 0, 0, 0, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (-27771559 / 22585631), 1, 0, 0, 0, 0, 0, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (648241 / 22585631), (-437678821 / 339442228), 1, 0, 0, 0, 0, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (648241 / 22585631), (14033799 / 339442228), (-2166940933 / 1590897411), 1, 0, 0, 0, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (648241 / 22585631), (14033799 / 339442228), (288021761 / 4772692233), (-29944838527 / 20579290062), 1, 0, 0, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (648241 / 22585631), (14033799 / 339442228), (288021761 / 4772692233), (1873109693 / 20579290062), (-1130812274039 / 715031755315), 1, 0, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (648241 / 22585631), (14033799 / 339442228), (288021761 / 4772692233), (1873109693 / 20579290062), (103945129681 / 715031755315), (-12494506680341 / 7076121402464), 1, 0, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (648241 / 22585631), (14033799 / 339442228), (288021761 / 4772692233), (1873109693 / 20579290062), (103945129681 / 715031755315), (1806128425959 / 7076121402464), (-112661471309279 / 54939557829277), 1, 0;
    (1 / 267), (13 / 1624), (1121 / 85109), (28119 / 1420990), (648241 / 22585631), (14033799 / 339442228), (288021761 / 4772692233), (1873109693 / 20579290062), (103945129681 / 715031755315), (1806128425959 / 7076121402464), (28860956740001 / 54939557829277), (-695665214109101 / 292539271632662), 1]

def pathShiftPivots : Fin 13 → ℚ :=
  ![(267 / 280), (406 / 445), (85109 / 97440), (142099 / 170218), (22585631 / 28419800), (84860557 / 112928155), (4772692233 / 6788844560), (3429881677 / 5302991370), (143006351063 / 246951480744), (1769030350616 / 3575158776575), (54939557829277 / 141522428049280), (146269635816331 / 549395578292770), (1673256372072519 / 5850785432653240)]

def pathShiftCertificate : GramCertificate 13 13 :=
  GramCertificate.ofLDL pathShiftLower pathShiftPivots

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pathShiftCertificate_valid :
    pathShiftCertificate.Valid (pathShiftFourteen.submatrix Fin.castSucc Fin.castSucc) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pathShiftPivots_pos : ∀ i, 0 < pathShiftPivots i := by decide +kernel

set_option maxRecDepth 100000 in
theorem pathShiftFourteen_symmetric : ∀ i j, pathShiftFourteen i j = pathShiftFourteen j i := by
  unfold pathShiftFourteen pathLaplacianFourteen centeringMatrix Matrix
  decide +kernel

set_option maxRecDepth 100000 in
theorem pathShiftFourteen_kernel : ∀ i, (∑ j, pathShiftFourteen i j * (1 : ℚ)) = 0 := by
  decide +kernel

/-- Full real PSD follows from the checked rational principal block and kernel. -/
theorem pathShiftFourteen_posSemidef :
    (pathShiftFourteen.map (fun q : ℚ => (q : ℝ))).PosSemidef :=
  rational_principal_gram_posSemidef pathShiftFourteen pathShiftFourteen_symmetric
    (fun _ => 1) pathShiftFourteen_kernel (by norm_num) pathShiftCertificate pathShiftCertificate_valid

/-- The incidence factor identifies the exact matrix with actual adjacent gaps. -/
def pathIncidenceCertificate : GramCertificate 14 13 :=
  ⟨fun _ => 1, fun t i => (if i = t.castSucc then 1 else 0) - (if i = t.succ then 1 else 0)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pathIncidenceCertificate_valid : pathIncidenceCertificate.Valid pathLaplacianFourteen := by
  decide +kernel

/-- The checked path matrix has exactly the sum of squared adjacent differences. -/
theorem pathLaplacianFourteen_quadratic (f : Fin 14 → ℝ) :
    quadraticValue (pathLaplacianFourteen.map (fun q : ℚ => (q : ℝ))) f =
      ∑ t : Fin 13, sweepGap f t ^ 2 := by
  rw [pathIncidenceCertificate.quadratic_identity pathLaplacianFourteen pathIncidenceCertificate_valid]
  have hinc (t : Fin 13) : (∑ i, (pathIncidenceCertificate.factor t i : ℝ) * f i) =
      f t.castSucc - f t.succ := by
    have hcast (i : Fin 14) : (pathIncidenceCertificate.factor t i : ℝ) =
        (if i = t.castSucc then 1 else 0) - (if i = t.succ then 1 else 0) := by
      dsimp only [pathIncidenceCertificate]
      split_ifs <;> norm_num
    simp_rw [hcast]
    simp [sub_mul, Finset.sum_sub_distrib]
  simp_rw [hinc]
  apply Finset.sum_congr rfl
  intro t _
  simp only [pathIncidenceCertificate, Rat.cast_one, sweepGap]
  ring

/-- The exact finite second-moment identity for the unweighted mean. -/
theorem sum_centered_fourteen (f : Fin 14 → ℝ) :
    (∑ i, (f i - (∑ j, f j) / 14) ^ 2) = (∑ i, f i ^ 2) - (∑ i, f i) ^ 2 / 14 := by
  let μ := (∑ j, f j) / 14
  have hp (i : Fin 14) : (f i - μ) ^ 2 = f i ^ 2 - 2 * μ * f i + μ ^ 2 := by ring
  change (∑ i, (f i - μ) ^ 2) = _
  simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [μ]
  ring

/-- The exact path Poincaré inequality on fourteen vertices. -/
theorem path_poincare_fourteen (f : Fin 14 → ℝ) :
    (∑ i, (f i - (∑ j, f j) / 14) ^ 2) ≤ 20 * ∑ t : Fin 13, sweepGap f t ^ 2 := by
  have h := quadraticValue_lower_of_centered_shift pathLaplacianFourteen (1 / 20)
    pathShiftFourteen_posSemidef f
  rw [pathLaplacianFourteen_quadratic] at h
  rw [sum_centered_fourteen]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat] at h
  linarith

/-- Centering at the weighted mean minimizes weighted squared deviations. -/
theorem sweepVariance_le_center {α : Type*} [Fintype α]
    (π f : α → ℝ) (hπ : ∑ i, π i = 1) (a : ℝ) :
    sweepVariance π f ≤ ∑ i, π i * (f i - a) ^ 2 := by
  have hp (i : α) : π i * (f i - a) ^ 2 = π i * f i ^ 2 - 2 * a * (π i * f i) + a ^ 2 * π i := by ring
  simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ, mul_one]
  rw [sweepVariance_eq_second_moment π f hπ]
  change _ ≤ _ - 2 * a * sweepMean π f + a ^ 2
  nlinarith [sq_nonneg (a - sweepMean π f)]

/-- A pointwise weight cap transfers the unweighted path bound to weighted variance. -/
theorem sweepVariance_le_twenty_gap_fourteen (π f : Fin 14 → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (pmax : ℝ) (hcap : ∀ i, π i ≤ pmax) :
    sweepVariance π f ≤ 20 * pmax * ∑ t : Fin 13, sweepGap f t ^ 2 := by
  have hpmax : 0 ≤ pmax := (hπ0 0).trans (hcap 0)
  calc
    _ ≤ ∑ i, π i * (f i - (∑ j, f j) / 14) ^ 2 := sweepVariance_le_center π f hπ _
    _ ≤ ∑ i, pmax * (f i - (∑ j, f j) / 14) ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcap i) (sq_nonneg _)
    _ = pmax * ∑ i, (f i - (∑ j, f j) / 14) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ pmax * (20 * ∑ t : Fin 13, sweepGap f t ^ 2) :=
      mul_le_mul_of_nonneg_left (path_poincare_fourteen f) hpmax
    _ = _ := by ring

/-- The minimizing sorted prefix obeys the refined fourteen-vertex factor. -/
theorem exists_refined_sweep_prefix (π f : Fin 14 → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1) (pmax : ℝ) (hcap : ∀ i, π i ≤ pmax)
    (c : Fin 14 → Fin 14 → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hcsym : ∀ i j, c i j = c j i) (hf : Monotone f) (hV : 0 < sweepVariance π f) :
    ∃ t : Fin 13, sweepBoundary c (sweepPrefix t) ≤
      20 * pmax * sweepEnergy c f / sweepVariance π f := by
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 13))
    (fun t => sweepBoundary c (sweepPrefix t)) ⟨0, Finset.mem_univ _⟩
  refine ⟨t, ?_⟩
  let b := sweepBoundary c (sweepPrefix t)
  have hb : 0 ≤ b := sweepBoundary_nonneg c hc0 _
  have hpmax : 0 ≤ pmax := (hπ0 0).trans (hcap 0)
  have hD : b * (∑ u, sweepGap f u ^ 2) ≤ sweepEnergy c f := by
    calc
      _ = ∑ u, b * sweepGap f u ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ u, sweepBoundary c (sweepPrefix u) * sweepGap f u ^ 2 :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (ht u (Finset.mem_univ _)) (sq_nonneg _)
      _ ≤ _ := sweep_prefix_gap_energy_le c hc0 hcsym f hf
  apply (le_div_iff₀ hV).mpr
  calc
    _ ≤ b * (20 * pmax * ∑ u, sweepGap f u ^ 2) :=
      mul_le_mul_of_nonneg_left (sweepVariance_le_twenty_gap_fourteen π f hπ0 hπ pmax hcap) hb
    _ = (20 * pmax) * (b * ∑ u, sweepGap f u ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)

/-- Refined spectral sweep at fourteen vertices. The denominator is only the
positive variance; ties and disconnected zero-energy graphs are included. -/
theorem exists_refined_weighted_sweep_cut
    (π : Fin 14 → ℝ) (hπpos : ∀ v, 0 < π v) (hπ : ∑ v, π v = 1)
    (pmax : ℝ) (hcap : ∀ i, π i ≤ pmax)
    (c : Fin 14 → Fin 14 → ℝ) (hc0 : ∀ v w, 0 ≤ c v w) (hcsym : ∀ v w, c v w = c w v)
    (f : Fin 14 → ℝ) (hV : 0 < sweepVariance π f) :
    ∃ S : Finset (Fin 14), S.Nonempty ∧ S ≠ Finset.univ ∧ sweepMass π S ≤ 1 / 2 ∧
      sweepBoundary c S ≤ 20 * pmax * sweepEnergy c f / sweepVariance π f := by
  let σ := Tuple.sort f
  have hπsum : ∑ v, (π ∘ σ) v = 1 := (Equiv.sum_comp σ π).trans hπ
  have hVsort : 0 < sweepVariance (π ∘ σ) (f ∘ σ) := by rwa [sweepVariance_permute]
  obtain ⟨t, ht⟩ := exists_refined_sweep_prefix (π ∘ σ) (f ∘ σ)
    (fun v => (hπpos (σ v)).le) hπsum pmax (fun v => hcap (σ v)) (fun i j => c (σ i) (σ j))
    (fun i j => hc0 (σ i) (σ j)) (fun i j => hcsym (σ i) (σ j))
    (Tuple.monotone_sort f) hVsort
  let S := (sweepPrefix t).map σ.toEmbedding
  have hS : S.Nonempty := Finset.map_nonempty.mpr (sweepPrefix_nonempty t)
  have hproper : S ≠ Finset.univ := by
    intro h
    apply sweepPrefix_ne_univ t
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi : σ i ∈ S := h ▸ Finset.mem_univ _
    simpa [S] using hi
  have hbound : sweepBoundary c S ≤ 20 * pmax * sweepEnergy c f / sweepVariance π f := by
    simpa only [sweepBoundary_permute, sweepEnergy_permute, sweepVariance_permute] using ht
  exact exists_balanced_sweep_cut π hπ c hcsym S hS hproper _ hbound

end DittertRybin
