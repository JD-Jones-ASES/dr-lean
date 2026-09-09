import DR.Rectangular.FourRowMinorantFaces
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# An explicit curve on the three-coordinate fixed-moment circle

The rational rotation preserves both the sum and the pair sum for all
real parameters. Its product derivative is twice the Vandermonde product.
Thus an extremum of the product along this curve has two equal entries.
This supplies the exact local step in the source's constrained three-face
extremum argument without importing a Lagrange-multiplier assertion.
-/

namespace DittertRybin
open scoped BigOperators
open scoped Topology
open Filter

noncomputable def threeMomentCoordinate (a b c t : ℝ) : ℝ :=
  ((1-t^2)*a+2*t^2*(b+c)+2*t*(b-c))/(1+3*t^2)

noncomputable def threeMomentCurve (r : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![threeMomentCoordinate (r 0) (r 1) (r 2) t,
    threeMomentCoordinate (r 1) (r 2) (r 0) t,
    threeMomentCoordinate (r 2) (r 0) (r 1) t]

theorem threeMomentCoordinate_den_pos (t : ℝ) : 0 < 1+3*t^2 := by positivity

@[simp] theorem threeMomentCoordinate_zero (a b c : ℝ) :
    threeMomentCoordinate a b c 0 = a := by simp [threeMomentCoordinate]

@[simp] theorem threeMomentCurve_zero (r : Fin 3 → ℝ) : threeMomentCurve r 0 = r := by
  funext i
  fin_cases i <;> simp [threeMomentCurve,Matrix.cons_val_two]

theorem threeMomentCurve_sum (r : Fin 3 → ℝ) (t : ℝ) :
    (∑ i, threeMomentCurve r t i) = ∑ i, r i := by
  norm_num [threeMomentCurve,threeMomentCoordinate,Fin.sum_univ_succ,Matrix.cons_val_two]
  field_simp
  ring

theorem threeMomentCurve_pair (r : Fin 3 → ℝ) (t : ℝ) :
    threeMomentCurve r t 0*threeMomentCurve r t 1+
      threeMomentCurve r t 0*threeMomentCurve r t 2+
      threeMomentCurve r t 1*threeMomentCurve r t 2 =
      r 0*r 1+r 0*r 2+r 1*r 2 := by
  norm_num [threeMomentCurve,threeMomentCoordinate,Matrix.cons_val_two]
  field_simp
  ring

theorem threeMomentCoordinate_continuous (a b c : ℝ) :
    Continuous (threeMomentCoordinate a b c) := by
  unfold threeMomentCoordinate
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro t
    exact (threeMomentCoordinate_den_pos t).ne'

theorem threeMomentCurve_continuous (r : Fin 3 → ℝ) : Continuous (threeMomentCurve r) := by
  apply continuous_pi
  intro i
  fin_cases i
  all_goals exact threeMomentCoordinate_continuous _ _ _

theorem threeMomentCoordinate_hasDerivAt (a b c : ℝ) :
    HasDerivAt (threeMomentCoordinate a b c) (2*(b-c)) 0 := by
  have ht := hasDerivAt_id (0 : ℝ)
  have ht2 := ht.pow 2
  have hnum := ((((ht2.const_sub 1).mul_const a).add
    ((ht2.const_mul 2).mul_const (b+c))).add ((ht.const_mul 2).mul_const (b-c)))
  have hden := (ht2.const_mul 3).const_add 1
  convert! hnum.div hden (by norm_num) using 1
  norm_num [threeMomentCoordinate]

theorem threeMomentCurve_product_hasDerivAt (r : Fin 3 → ℝ) :
    HasDerivAt (fun t => ∏ i, threeMomentCurve r t i)
      (2*(r 0-r 1)*(r 0-r 2)*(r 1-r 2)) 0 := by
  have h := ((threeMomentCoordinate_hasDerivAt (r 0) (r 1) (r 2)).mul
    (threeMomentCoordinate_hasDerivAt (r 1) (r 2) (r 0))).mul
    (threeMomentCoordinate_hasDerivAt (r 2) (r 0) (r 1))
  convert! h using 1
  · funext t
    simp [threeMomentCurve,Fin.prod_univ_succ,mul_assoc]
  · simp only [Pi.mul_apply,threeMomentCoordinate_zero]
    ring

/-- Exact constrained-product local extremum obstruction, valid even for signed rows. -/
theorem threeMomentCurve_product_extremum_repeated (r : Fin 3 → ℝ)
    (h : IsLocalExtr (fun t => ∏ i, threeMomentCurve r t i) 0) :
    r 0 = r 1 ∨ r 0 = r 2 ∨ r 1 = r 2 := by
  have hz := h.hasDerivAt_eq_zero (threeMomentCurve_product_hasDerivAt r)
  rcases mul_eq_zero.mp hz with hz | hz
  · rcases mul_eq_zero.mp hz with hz | hz
    · have := (mul_eq_zero.mp hz).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
      exact Or.inl (sub_eq_zero.mp this)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hz))

/-- A fixed first/two-coordinate-moment slice with a continuous coordinate
feasibility constraint. This is the genuine closed set used below. -/
def threeMomentFeasible (s t : ℝ) (φ : ℝ → ℝ) : Set (Fin 3 → ℝ) :=
  {r | (∀ i, 0 ≤ r i) ∧ (∑ i, r i) = s ∧
    r 0*r 1+r 0*r 2+r 1*r 2=t ∧ ∀ i, 0 ≤ φ (r i)}

/-- At a strictly feasible point, the explicit fixed-moment curve remains
inside the actual closed feasible set for all sufficiently small parameters. -/
theorem threeMomentCurve_eventually_feasible (s t : ℝ) (φ : ℝ → ℝ)
    (hφ : Continuous φ) (r : Fin 3 → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∑ i, r i = s)
    (ht : r 0*r 1+r 0*r 2+r 1*r 2=t) (hp : ∀ i, 0 < φ (r i)) :
    ∀ᶠ x in 𝓝 (0 : ℝ), threeMomentCurve r x ∈ threeMomentFeasible s t φ := by
  have hc (i : Fin 3) : Continuous (fun x => threeMomentCurve r x i) :=
    (continuous_apply i).comp (threeMomentCurve_continuous r)
  have hrow : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ i, 0 < threeMomentCurve r x i := by
    rw [eventually_all]
    intro i
    exact (isOpen_lt continuous_const (hc i)).mem_nhds (by simpa using hr i)
  have hcon : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ i, 0 < φ (threeMomentCurve r x i) := by
    rw [eventually_all]
    intro i
    exact (isOpen_lt continuous_const (hφ.comp (hc i))).mem_nhds (by simpa using hp i)
  filter_upwards [hrow,hcon] with x hx hpx
  exact ⟨fun i => (hx i).le,(threeMomentCurve_sum r x).trans hs,
    (threeMomentCurve_pair r x).trans ht,fun i => (hpx i).le⟩

/-- A constrained product extremum with inactive nonnegative constraints has
two equal coordinates. The premise is an extremum of the explicit cubic
product on the fixed-moment set, without an assumed minorant bound. -/
theorem threeMomentFeasible_product_extremum_repeated (s t : ℝ) (φ : ℝ → ℝ)
    (hφ : Continuous φ) (r : Fin 3 → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∑ i, r i = s)
    (ht : r 0*r 1+r 0*r 2+r 1*r 2=t) (hp : ∀ i, 0 < φ (r i))
    (hext : IsExtrOn (fun u => ∏ i, u i) (threeMomentFeasible s t φ) r) :
    r 0 = r 1 ∨ r 0 = r 2 ∨ r 1 = r 2 := by
  apply threeMomentCurve_product_extremum_repeated r
  have he := threeMomentCurve_eventually_feasible s t φ hφ r hr hs ht hp
  rcases hext with hmin | hmax
  · left
    filter_upwards [he] with x hx
    simpa using hmin hx
  · right
    filter_upwards [he] with x hx
    simpa using hmax hx

end DittertRybin
