import DR.Square.StableClosure
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Differentiation and boundary specialization preserve H-stability

Positive directional derivatives are controlled by Gauss–Lucas on the line
`p(z + t u)`. Homogeneous limit closure then lets the positive direction tend
to a coordinate vector, and lets a positive coordinate scaling tend to zero.
This proves the closure required by Gurvits (2008), Section 4, Fact 4.9:
https://arxiv.org/abs/0711.3496v2.
-/

open scoped BigOperators Topology Polynomial
open Finset Set Filter

namespace DittertRybin

private theorem coeff_prod_sum_of_natDegree_le {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → Polynomial R) (d : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hf i (by simp))]
    · rw [ih (fun j hj => hf j (by simp [hj]))]
    · exact (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun j hj => hf j (by simp [hj]))

private theorem affine_pow_degree_coeff {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 ∧
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ n).coeff n = b ^ n := by
  have hd : (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
    exact Polynomial.natDegree_add_le_of_degree_le (by simp) (by
      exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
  refine ⟨hd, ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Polynomial.coeff_mul_add_eq_of_natDegree_le]
    · simp [ih, pow_succ]
    · exact (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left n hd)
    · exact hd

/-- A complex affine line with real direction through a complex vector. -/
noncomputable def affineLinePolynomial {σ : Type*} (p : MvPolynomial σ ℝ)
    (z : σ → ℂ) (u : σ → ℝ) : Polynomial ℂ :=
  p.eval₂ (Polynomial.C.comp (algebraMap ℝ ℂ))
    (fun j => Polynomial.C (z j) + Polynomial.C ((algebraMap ℝ ℂ) (u j)) * Polynomial.X)

theorem affineLinePolynomial_eval {σ : Type*} (p : MvPolynomial σ ℝ)
    (z : σ → ℂ) (u : σ → ℝ) (t : ℂ) :
    (affineLinePolynomial p z u).eval t =
      p.eval₂ (algebraMap ℝ ℂ) (fun j => z j + (algebraMap ℝ ℂ) (u j) * t) := by
  change (Polynomial.evalRingHom t) (_ : Polynomial ℂ) = _
  rw [affineLinePolynomial, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext j
    simp

/-- The top line coefficient is evaluation at the direction, even when it vanishes. -/
theorem affineLinePolynomial_degree_coeff {σ : Type*} {p : MvPolynomial σ ℝ}
    {d : ℕ} (hp : p.IsHomogeneous d) (z : σ → ℂ) (u : σ → ℝ) :
    (affineLinePolynomial p z u).natDegree ≤ d ∧
    (affineLinePolynomial p z u).coeff d = (algebraMap ℝ ℂ) (p.eval u) := by
  classical
  let f (j : σ) : Polynomial ℂ :=
    Polynomial.C (z j) + Polynomial.C ((algebraMap ℝ ℂ) (u j)) * Polynomial.X
  have hpow (j : σ) (n : ℕ) : (f j ^ n).natDegree ≤ n :=
    Polynomial.natDegree_pow_le.trans (by
      simpa [f] using Nat.mul_le_mul_left n (affine_pow_degree_coeff (z j) ((algebraMap ℝ ℂ) (u j)) n).1)
  have hprod (m : σ →₀ ℕ) :
      (∏ j ∈ m.support, f j ^ m j).natDegree ≤ ∑ j ∈ m.support, m j :=
    (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => hpow j (m j))
  have heq : affineLinePolynomial p z u =
      ∑ m ∈ p.support, Polynomial.C ((algebraMap ℝ ℂ) (p.coeff m)) *
        ∏ j ∈ m.support, f j ^ m j := by
    simp [affineLinePolynomial, MvPolynomial.eval₂_eq, f, RingHom.comp_apply]
  constructor
  · rw [heq]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro m hm
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((hprod m).trans_eq (hp.degree_eq_sum_deg_support hm).symm)
  · rw [heq, Polynomial.finsetSum_coeff, MvPolynomial.eval_eq, map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Polynomial.coeff_C_mul, hp.degree_eq_sum_deg_support hm,
      coeff_prod_sum_of_natDegree_le _ _ _ (fun j _ => hpow j (m j))]
    simp [f, (affine_pow_degree_coeff _ _ _).2, map_mul, map_prod, map_pow]

/-- The actual formal directional derivative. -/
noncomputable def directionalDerivative {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (u : σ → ℝ) : MvPolynomial σ ℝ :=
  ∑ j, MvPolynomial.C (u j) * MvPolynomial.pderiv j p

theorem affineLinePolynomial_derivative {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (z : σ → ℂ) (u : σ → ℝ) :
    (affineLinePolynomial p z u).derivative =
      ∑ j, Polynomial.C ((algebraMap ℝ ℂ) (u j)) *
        affineLinePolynomial (MvPolynomial.pderiv j p) z u := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [affineLinePolynomial]
  | add p q hp hq =>
    simpa [affineLinePolynomial, mul_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    let E : MvPolynomial σ ℝ →+* Polynomial ℂ :=
      MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℝ ℂ))
        (fun j => Polynomial.C (z j) + Polynomial.C ((algebraMap ℝ ℂ) (u j)) * Polynomial.X)
    change (E (p * MvPolynomial.X k)).derivative =
      ∑ j, Polynomial.C ((algebraMap ℝ ℂ) (u j)) * E (MvPolynomial.pderiv j (p * MvPolynomial.X k))
    change (E p).derivative = ∑ j, Polynomial.C ((algebraMap ℝ ℂ) (u j)) * E (MvPolynomial.pderiv j p) at hp
    have hX : (E (MvPolynomial.X k)).derivative = Polynomial.C ((algebraMap ℝ ℂ) (u k)) := by
      simp [E]
    rw [map_mul, Polynomial.derivative_mul, hp, hX]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    have hfirst : (∑ j, Polynomial.C ((algebraMap ℝ ℂ) (u j)) * E (MvPolynomial.pderiv j p)) *
        E (MvPolynomial.X k) = ∑ j, Polynomial.C ((algebraMap ℝ ℂ) (u j)) *
          (E (MvPolynomial.pderiv j p) * E (MvPolynomial.X k)) := by
      simp [Finset.sum_mul, mul_assoc]
    rw [hfirst]
    congr 1
    have hsparse (j : σ) : E (MvPolynomial.pderiv j (MvPolynomial.X k)) = if k = j then 1 else 0 := by
      by_cases h : k = j
      · subst j
        simp
      · simp [MvPolynomial.pderiv_X_of_ne h, h]
    simp_rw [hsparse]
    simp [mul_comm]

theorem affineLinePolynomial_derivative_eval_zero {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (z : σ → ℂ) (u : σ → ℝ) :
    (affineLinePolynomial p z u).derivative.eval 0 =
      (directionalDerivative p u).eval₂ (algebraMap ℝ ℂ) z := by
  rw [affineLinePolynomial_derivative]
  simp [directionalDerivative, Polynomial.eval_finsetSum, affineLinePolynomial_eval]

theorem directionalDerivative_isHomogeneous {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (u : σ → ℝ) :
    (directionalDerivative p u).IsHomogeneous (d - 1) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  simpa using (MvPolynomial.isHomogeneous_C σ (u j)).mul (hp.pderiv (i := j))

theorem directionalDerivative_nonnegative {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} (hp : HasNonnegativeCoefficients p) {u : σ → ℝ}
    (hu : ∀ j, 0 ≤ u j) : HasNonnegativeCoefficients (directionalDerivative p u) := by
  apply hasNonnegativeCoefficients_sum
  intro j hj
  exact (hp.pderiv j).C_mul (hu j)

/-- A nonconstant polynomial whose roots lie strictly to the left has a
nonzero derivative at zero. This is the precise Gauss–Lucas use below. -/
theorem derivative_eval_zero_ne_zero_of_roots_re_neg {q : Polynomial ℂ}
    (hd : 0 < q.degree) (hr : ∀ z : ℂ, q.eval z = 0 → z.re < 0) :
    q.derivative.eval 0 ≠ 0 := by
  intro hz
  have hmem : (0 : ℂ) ∈ q.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨Polynomial.derivative_ne_zero.mpr
      (Polynomial.natDegree_pos_iff_degree_pos.mpr hd).ne', hz⟩
  have hconvex : Convex ℝ {z : ℂ | z.re < 0} :=
    convex_halfSpace_lt ⟨Complex.add_re, fun a z => by simp⟩ 0
  have hsub : q.rootSet ℂ ⊆ {z : ℂ | z.re < 0} := by
    intro z hz
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hz
    exact hr z hz.2
  have hlt := (convexHull_min hsub hconvex)
    (Polynomial.rootSet_derivative_subset_convexHull_rootSet hd hmem)
  exact (lt_irrefl (0 : ℝ)) hlt

/-- Positive directions yield genuinely stable directional derivatives. -/
theorem directionalDerivative_hStable {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hc : HasNonnegativeCoefficients p) (hp : HStable p) (hd : 0 < d)
    {u : σ → ℝ} (hu : ∀ j, 0 < u j) : HStable (directionalDerivative p u) := by
  intro z hz
  have htop := (affineLinePolynomial_degree_coeff hhom z u).2
  have hpupos := mvPolynomial_eval_pos hc hp.ne_zero hu
  have hcoeff : (affineLinePolynomial p z u).coeff d ≠ 0 := by
    rw [htop]
    exact Complex.ofReal_ne_zero.mpr hpupos.ne'
  have hdegree : 0 < (affineLinePolynomial p z u).degree :=
    lt_of_lt_of_le (by exact_mod_cast hd) (Polynomial.le_degree_of_ne_zero hcoeff)
  rw [← affineLinePolynomial_derivative_eval_zero]
  apply derivative_eval_zero_ne_zero_of_roots_re_neg hdegree
  intro t ht
  by_contra hnot
  have ht0 : 0 ≤ t.re := le_of_not_gt hnot
  rw [affineLinePolynomial_eval] at ht
  apply hp _ (fun j => ?_) ht
  simpa [Complex.add_re, Complex.mul_re] using
    add_pos_of_pos_of_nonneg (hz j) (mul_nonneg (hu j).le ht0)

theorem directionalDerivative_single {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i : σ) :
    directionalDerivative p (fun j => if j = i then 1 else 0) = MvPolynomial.pderiv i p := by
  simp [directionalDerivative, apply_ite]

theorem tendsto_directionalDerivative_eval {σ ι : Type*} [Fintype σ]
    {l : Filter ι} (p : MvPolynomial σ ℝ) {u : ι → σ → ℝ} {v : σ → ℝ}
    (hu : ∀ j, Tendsto (fun a => u a j) l (𝓝 (v j))) (z : σ → ℂ) :
    Tendsto (fun a => (directionalDerivative p (u a)).eval₂ (algebraMap ℝ ℂ) z) l
      (𝓝 ((directionalDerivative p v).eval₂ (algebraMap ℝ ℂ) z)) := by
  simp only [directionalDerivative, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C]
  exact tendsto_finsetSum _ fun j _ =>
    ((Complex.continuous_ofReal.tendsto _).comp (hu j)).mul tendsto_const_nhds

/-- Coordinate derivatives preserve H-stability, with the necessary zero alternative. -/
theorem pderiv_zero_or_hStable {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hc : HasNonnegativeCoefficients p) (hp : p = 0 ∨ HStable p) (i : σ) :
    MvPolynomial.pderiv i p = 0 ∨ HStable (MvPolynomial.pderiv i p) := by
  classical
  rcases hp with rfl | hp
  · simp
  by_cases hd : d = 0
  · subst d
    have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr hhom)
    left
    rw [hconstant, MvPolynomial.pderiv_C]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let u (a : ℕ) (j : σ) : ℝ := (if j = i then 1 else 0) + 1 / ((a : ℝ) + 1)
  have hu (a : ℕ) (j : σ) : 0 < u a j := by
    dsimp [u]
    split_ifs <;> positivity
  have hlim (j : σ) : Tendsto (fun a => u a j) atTop (𝓝 (if j = i then 1 else 0)) := by
    simpa [u] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply zero_or_hStable_of_tendsto_eval (l := atTop)
    (P := fun a => directionalDerivative p (u a))
    (fun a => directionalDerivative_isHomogeneous hhom (u a))
    (fun a => Or.inr (directionalDerivative_hStable hhom hc hp hdpos (hu a)))
    (hc.pderiv i)
  intro z
  simpa only [directionalDerivative_single] using tendsto_directionalDerivative_eval p hlim z

/-- Scale each variable by its assigned real scalar. Zero scalars are allowed. -/
noncomputable def scaleVariables {σ : Type*} (p : MvPolynomial σ ℝ)
    (a : σ → ℝ) : MvPolynomial σ ℝ :=
  p.eval₂ MvPolynomial.C (fun j => MvPolynomial.C (a j) * MvPolynomial.X j)

theorem scaleVariables_eval₂ {σ : Type*} (p : MvPolynomial σ ℝ)
    (a : σ → ℝ) (z : σ → ℂ) :
    (scaleVariables p a).eval₂ (algebraMap ℝ ℂ) z =
      p.eval₂ (algebraMap ℝ ℂ) (fun j => (algebraMap ℝ ℂ) (a j) * z j) := by
  change (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z) (_ : MvPolynomial σ ℝ) = _
  rw [scaleVariables, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext c
    simp
  · funext j
    simp

theorem scaleVariables_isHomogeneous {σ : Type*} {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (a : σ → ℝ) : (scaleVariables p a).IsHomogeneous d := by
  simpa [scaleVariables] using hp.eval₂ MvPolynomial.C
    (fun j => MvPolynomial.C (a j) * MvPolynomial.X j)
    (fun c => MvPolynomial.isHomogeneous_C σ c)
    (fun j => (MvPolynomial.isHomogeneous_C σ (a j)).mul (MvPolynomial.isHomogeneous_X ℝ j))

theorem scaleVariables_nonnegative {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) {a : σ → ℝ} (ha : ∀ j, 0 ≤ a j) :
    HasNonnegativeCoefficients (scaleVariables p a) := by
  exact hp.eval₂ _ (fun j => (hasNonnegativeCoefficients_X j).C_mul (ha j))

theorem scaleVariables_hStable {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HStable p) {a : σ → ℝ} (ha : ∀ j, 0 < a j) : HStable (scaleVariables p a) := by
  intro z hz
  rw [scaleVariables_eval₂]
  apply hp
  intro j
  simpa using mul_pos (ha j) (hz j)

theorem tendsto_scaleVariables_eval {σ ι : Type*} {l : Filter ι}
    (p : MvPolynomial σ ℝ) {a : ι → σ → ℝ} {b : σ → ℝ}
    (ha : ∀ j, Tendsto (fun t => a t j) l (𝓝 (b j))) (z : σ → ℂ) :
    Tendsto (fun t => (scaleVariables p (a t)).eval₂ (algebraMap ℝ ℂ) z) l
      (𝓝 ((scaleVariables p b).eval₂ (algebraMap ℝ ℂ) z)) := by
  simp_rw [scaleVariables_eval₂]
  simp only [MvPolynomial.eval₂_eq_eval_map]
  apply ((MvPolynomial.map (algebraMap ℝ ℂ) p).continuous_eval.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro j
  exact ((Complex.continuous_ofReal.tendsto _).comp (ha j)).mul tendsto_const_nhds

/-- Nonnegative coordinate scalings, including boundary specialization, preserve
H-stability unless the resulting polynomial vanishes identically. -/
theorem scaleVariables_zero_or_hStable {σ : Type*}
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hc : HasNonnegativeCoefficients p) (hp : p = 0 ∨ HStable p)
    {b : σ → ℝ} (hb : ∀ j, 0 ≤ b j) :
    scaleVariables p b = 0 ∨ HStable (scaleVariables p b) := by
  rcases hp with rfl | hp
  · simp [scaleVariables]
  let a (t : ℕ) (j : σ) : ℝ := b j + 1 / ((t : ℝ) + 1)
  have ha (t : ℕ) (j : σ) : 0 < a t j := by
    exact add_pos_of_nonneg_of_pos (hb j) (by positivity)
  have hlim (j : σ) : Tendsto (fun t => a t j) atTop (𝓝 (b j)) := by
    simpa [a] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact zero_or_hStable_of_tendsto_eval (l := atTop)
    (fun t => scaleVariables_isHomogeneous hhom (a t))
    (fun t => Or.inr (scaleVariables_hStable hp (ha t)))
    (scaleVariables_nonnegative hc hb) (tendsto_scaleVariables_eval p hlim)

theorem derivativeAtZero_eq_scaleVariables {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i : σ) :
    derivativeAtZero p i =
      scaleVariables (MvPolynomial.pderiv i p) (fun j => if j = i then 0 else 1) := by
  unfold derivativeAtZero scaleVariables
  congr 1
  funext j
  split_ifs with h <;> simp [h]

/-- The derivative-plus-zero-specialization closure needed for capacity descent.
Every premise concerns the original polynomial; no stability closure is assumed. -/
theorem derivativeAtZero_zero_or_hStable {σ : Type*} [Fintype σ] [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hc : HasNonnegativeCoefficients p) (hp : p = 0 ∨ HStable p) (i : σ) :
    derivativeAtZero p i = 0 ∨ HStable (derivativeAtZero p i) := by
  rw [derivativeAtZero_eq_scaleVariables]
  exact scaleVariables_zero_or_hStable (hhom.pderiv (i := i)) (hc.pderiv i)
    (pderiv_zero_or_hStable hhom hc hp i) (fun j => by split_ifs <;> norm_num)

/-- Formal differentiation commutes with taking a single-variable slice. -/
theorem singleVariableSlice_derivative {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i : σ) (x : σ → ℝ) :
    (singleVariableSlice p i x).derivative =
      singleVariableSlice (MvPolynomial.pderiv i p) i x := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [singleVariableSlice]
  | add p q hp hq => simpa [singleVariableSlice] using congrArg₂ (· + ·) hp hq
  | mul_X p j hp =>
    simp only [singleVariableSlice] at hp ⊢
    by_cases h : j = i
    · subst j
      simp [Polynomial.derivative_mul, hp, mul_comm]
    · simp [Polynomial.derivative_mul, hp, h, mul_comm]

/-- The slice derivative at zero is exactly evaluation of the differentiated,
zero-specialized multivariate polynomial used by the closure theorem. -/
theorem derivativeAtZero_eval {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i : σ) (x : σ → ℝ) :
    (derivativeAtZero p i).eval x = (singleVariableSlice p i x).derivative.eval 0 := by
  rw [singleVariableSlice_derivative]
  have hs := singleVariableSlice_eval₂ (MvPolynomial.pderiv i p) i x (RingHom.id ℝ) 0
  simp only [Polynomial.eval₂_id, RingHom.id_apply] at hs
  rw [hs]
  change (MvPolynomial.eval₂Hom (RingHom.id ℝ) x)
    ((MvPolynomial.pderiv i p).eval₂ MvPolynomial.C
      (fun j => if j = i then 0 else MvPolynomial.X j)) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext c
    simp
  · funext j
    split_ifs with h <;> simp [h]

end DittertRybin
