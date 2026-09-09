import DR.Square.NormComparison
import Mathlib.Data.Finsupp.Interval
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Closure prerequisites for homogeneous H-stability

The norm comparison gives actual limit closure with a zero-polynomial
alternative. The differentiated and zero-specialized polynomial is defined
explicitly, and its algebraic data are preserved. H-stability of that
derivative operation requires the further regularization/Gauss–Lucas step.
-/

open scoped BigOperators Topology
open Finset Set Filter

namespace DittertRybin

theorem mvPolynomial_eval_nonneg {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) {x : σ → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ p.eval x := by
  rw [MvPolynomial.eval_eq]
  exact Finset.sum_nonneg fun m _ => mul_nonneg (hp m)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

theorem mvPolynomial_eval_pos {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) (hp0 : p ≠ 0) {x : σ → ℝ} (hx : ∀ i, 0 < x i) :
    0 < p.eval x := by
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_pos'
  · exact fun m _ => mul_nonneg (hp m) (Finset.prod_nonneg fun i _ => (pow_pos (hx i) _).le)
  · obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hp0
    refine ⟨m, hm, mul_pos ?_ (Finset.prod_pos fun i _ => pow_pos (hx i) _)⟩
    exact lt_of_le_of_ne (hp m) (MvPolynomial.mem_support_iff.mp hm).symm

/-- Pointwise polynomial evaluation limits inherit the norm comparison and hence
H-stability, unless the limit polynomial is zero. -/
theorem zero_or_hStable_of_tendsto_eval {σ ι : Type*} {l : Filter ι} [NeBot l]
    {P : ι → MvPolynomial σ ℝ} {p : MvPolynomial σ ℝ} {d : ι → ℕ}
    (hhom : ∀ a, (P a).IsHomogeneous (d a)) (hstable : ∀ a, P a = 0 ∨ HStable (P a))
    (hp : HasNonnegativeCoefficients p)
    (hlim : ∀ z : σ → ℂ, Tendsto (fun a => (P a).eval₂ (algebraMap ℝ ℂ) z) l
      (𝓝 (p.eval₂ (algebraMap ℝ ℂ) z))) : p = 0 ∨ HStable p := by
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  · right
    intro z hz
    have hpos := mvPolynomial_eval_pos hp hp0 hz
    have hnorm := le_of_tendsto_of_tendsto
      (hlim (fun j => (algebraMap ℝ ℂ) (z j).re)).norm (hlim z).norm
      (Filter.Eventually.of_forall (fun a => by
        rcases hstable a with ha | ha
        · simp [ha]
        · exact homogeneous_hStable_norm_comparison (hhom a) ha hz))
    rw [eval₂_of_real_vector] at hnorm
    have hnorm' : p.eval (fun j => (z j).re) ≤ ‖p.eval₂ (algebraMap ℝ ℂ) z‖ := by
      simpa [Real.norm_of_nonneg hpos.le] using hnorm
    intro hzero
    rw [hzero, norm_zero] at hnorm'
    exact (not_le_of_gt hpos) hnorm'

/-- A common finite support turns coefficient limits into evaluation limits. -/
theorem eval₂_eq_sum_of_support_subset {σ : Type*} {p : MvPolynomial σ ℝ}
    {s : Finset (σ →₀ ℕ)} (hs : p.support ⊆ s) (z : σ → ℂ) :
    p.eval₂ (algebraMap ℝ ℂ) z =
      ∑ m ∈ s, (algebraMap ℝ ℂ) (p.coeff m) * ∏ j ∈ m.support, z j ^ m j := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Finset.sum_subset hs
  intro m hm hnot
  have hc : p.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hnot
  simp [hc]

theorem tendsto_eval₂_of_coefficientwise {σ ι : Type*} {l : Filter ι}
    {P : ι → MvPolynomial σ ℝ} {p : MvPolynomial σ ℝ}
    {s : Finset (σ →₀ ℕ)} (hP : ∀ a, (P a).support ⊆ s) (hp : p.support ⊆ s)
    (hlim : ∀ m, Tendsto (fun a => (P a).coeff m) l (𝓝 (p.coeff m))) (z : σ → ℂ) :
    Tendsto (fun a => (P a).eval₂ (algebraMap ℝ ℂ) z) l
      (𝓝 (p.eval₂ (algebraMap ℝ ℂ) z)) := by
  simp_rw [eval₂_eq_sum_of_support_subset hp z]
  have heq : (fun a => (P a).eval₂ (algebraMap ℝ ℂ) z) =
      fun a => ∑ m ∈ s, (algebraMap ℝ ℂ) ((P a).coeff m) * ∏ j ∈ m.support, z j ^ m j := by
    funext a
    exact eval₂_eq_sum_of_support_subset (hP a) z
  rw [heq]
  apply tendsto_finsetSum
  intro m hm
  exact ((Complex.continuous_ofReal.tendsto _).comp (hlim m)).mul tendsto_const_nhds

/-- A finite box containing every degree-d monomial, for finitely many variables. -/
noncomputable def homogeneousExponentBox (σ : Type*) [Fintype σ] (d : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact Finset.Icc 0 (Finsupp.equivFunOnFinite.symm (fun _ : σ => d))

theorem support_subset_homogeneousExponentBox {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d) :
    p.support ⊆ homogeneousExponentBox σ d := by
  classical
  intro m hm
  unfold homogeneousExponentBox
  apply Finset.mem_Icc.mpr
  constructor
  · intro j
    exact Nat.zero_le _
  change ∀ j, m j ≤ d
  intro j
  calc
    m j ≤ ∑ k ∈ m.support, m k := by
      by_cases hj : j ∈ m.support
      · exact Finset.single_le_sum (fun k _ => Nat.zero_le (m k)) hj
      · rw [Finsupp.notMem_support_iff.mp hj]
        exact Nat.zero_le _
    _ = d := (hp.degree_eq_sum_deg_support hm).symm

theorem isHomogeneous_of_coefficientwise_limit {σ ι : Type*} {l : Filter ι} [NeBot l]
    {P : ι → MvPolynomial σ ℝ} {p : MvPolynomial σ ℝ} {d : ℕ}
    (hP : ∀ a, (P a).IsHomogeneous d)
    (hlim : ∀ m, Tendsto (fun a => (P a).coeff m) l (𝓝 (p.coeff m))) : p.IsHomogeneous d := by
  intro m hm
  by_contra hd
  have hzero : ∀ a, (P a).coeff m = 0 := by
    intro a
    by_contra hne
    exact hd (hP a hne)
  have hlimzero : Tendsto (fun a => (P a).coeff m) l (𝓝 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact hm (tendsto_nhds_unique (hlim m) hlimzero)

theorem nonnegativeCoefficients_of_coefficientwise_limit {σ ι : Type*} {l : Filter ι} [NeBot l]
    {P : ι → MvPolynomial σ ℝ} {p : MvPolynomial σ ℝ}
    (hP : ∀ a, HasNonnegativeCoefficients (P a))
    (hlim : ∀ m, Tendsto (fun a => (P a).coeff m) l (𝓝 (p.coeff m))) :
    HasNonnegativeCoefficients p := by
  intro m
  exact ge_of_tendsto (hlim m) (Filter.Eventually.of_forall fun a => hP a m)

/-- Coefficientwise limits preserve all three data: homogeneous degree,
nonnegative coefficients, and H-stability or the zero polynomial. -/
theorem coefficientwise_limit_preserves_homogeneous_hStable {σ ι : Type*} [Fintype σ]
    {l : Filter ι} [NeBot l] {P : ι → MvPolynomial σ ℝ} {p : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : ∀ a, (P a).IsHomogeneous d) (hc : ∀ a, HasNonnegativeCoefficients (P a))
    (hstable : ∀ a, P a = 0 ∨ HStable (P a))
    (hlim : ∀ m, Tendsto (fun a => (P a).coeff m) l (𝓝 (p.coeff m))) :
    p.IsHomogeneous d ∧ HasNonnegativeCoefficients p ∧ (p = 0 ∨ HStable p) := by
  have hpHom := isHomogeneous_of_coefficientwise_limit (l := l) hhom hlim
  have hpC := nonnegativeCoefficients_of_coefficientwise_limit (l := l) hc hlim
  refine ⟨hpHom, hpC, zero_or_hStable_of_tendsto_eval (l := l) hhom hstable hpC ?_⟩
  intro z
  exact tendsto_eval₂_of_coefficientwise
    (fun a => support_subset_homogeneousExponentBox (hhom a))
    (support_subset_homogeneousExponentBox hpHom) hlim z

theorem hasNonnegativeCoefficients_zero {σ : Type*} :
    HasNonnegativeCoefficients (0 : MvPolynomial σ ℝ) := by
  intro m
  simp

theorem hasNonnegativeCoefficients_C {σ : Type*} {c : ℝ} (hc : 0 ≤ c) :
    HasNonnegativeCoefficients (MvPolynomial.C c : MvPolynomial σ ℝ) := by
  simpa using (hasNonnegativeCoefficients_one (σ := σ)).C_mul hc

theorem HasNonnegativeCoefficients.pow {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) (n : ℕ) : HasNonnegativeCoefficients (p ^ n) := by
  induction n with
  | zero => simpa using hasNonnegativeCoefficients_one (σ := σ)
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hp

theorem HasNonnegativeCoefficients.eval₂ {σ τ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) (g : σ → MvPolynomial τ ℝ)
    (hg : ∀ i, HasNonnegativeCoefficients (g i)) :
    HasNonnegativeCoefficients (p.eval₂ MvPolynomial.C g) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply hasNonnegativeCoefficients_sum
  intro m hm
  apply (hasNonnegativeCoefficients_C (hp m)).mul
  apply hasNonnegativeCoefficients_prod
  intro j hj
  exact (hg j).pow (m j)

theorem HasNonnegativeCoefficients.pderiv {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) (i : σ) :
    HasNonnegativeCoefficients (MvPolynomial.pderiv i p) := by
  intro m
  rw [MvPolynomial.coeff_pderiv]
  exact mul_nonneg (hp _) (by positivity)

/-- Differentiate a variable and then specialize that variable to zero.
The polynomial remains indexed by σ but no longer uses coordinate i. -/
noncomputable def derivativeAtZero {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i : σ) : MvPolynomial σ ℝ :=
  (MvPolynomial.pderiv i p).eval₂ MvPolynomial.C
    (fun j => if j = i then 0 else MvPolynomial.X j)

theorem derivativeAtZero_zero {σ : Type*} [DecidableEq σ] (i : σ) :
    derivativeAtZero (0 : MvPolynomial σ ℝ) i = 0 := by
  simp [derivativeAtZero]

theorem derivativeAtZero_nonnegative {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} (hp : HasNonnegativeCoefficients p) (i : σ) :
    HasNonnegativeCoefficients (derivativeAtZero p i) := by
  apply (hp.pderiv i).eval₂
  intro j
  split_ifs
  · exact hasNonnegativeCoefficients_zero
  · exact hasNonnegativeCoefficients_X j

theorem derivativeAtZero_isHomogeneous {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (i : σ) :
    (derivativeAtZero p i).IsHomogeneous (d - 1) := by
  have hg (j : σ) : (if j = i then (0 : MvPolynomial σ ℝ) else MvPolynomial.X j).IsHomogeneous 1 := by
    split_ifs
    · exact MvPolynomial.isHomogeneous_zero σ ℝ 1
    · exact MvPolynomial.isHomogeneous_X ℝ j
  simpa [derivativeAtZero] using (hp.pderiv (i := i)).eval₂ MvPolynomial.C
    (fun j => if j = i then 0 else MvPolynomial.X j)
    (fun c => MvPolynomial.isHomogeneous_C σ c) hg

end DittertRybin
