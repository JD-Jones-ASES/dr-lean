import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Real-rooted derivative and Newton prerequisites

Multiplicity-aware Rolle theory preserves real splitting under derivatives.
The logarithmic derivative and finite Cauchy--Schwarz inequality then give
the degree-sharp Laguerre inequality. No root or coefficient inequality is
assumed, and repeated roots and evaluation at a root are included.
-/

namespace DittertRybin
open scoped BigOperators
open Polynomial Filter Topology

theorem real_splits_derivative {p : ℝ[X]} (hp : p.Splits) : p.derivative.Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  apply le_antisymm (Polynomial.card_roots' _)
  have hr := p.card_roots_le_derivative
  rw [Polynomial.splits_iff_card_roots.mp hp] at hr
  rw [Polynomial.natDegree_derivative]
  omega

theorem real_splits_iterate_derivative {p : ℝ[X]} (hp : p.Splits) (k : ℕ) :
    (Polynomial.derivative^[k] p).Splits := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
      simpa only [Function.iterate_succ_apply'] using real_splits_derivative ih

theorem multiset_sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) :
    s.sum^2 ≤ (s.card:ℝ)*(s.map (fun x => x^2)).sum := by
  refine Quotient.inductionOn s ?_
  intro l
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i : Fin l.length => l[i.val])
  have h1 : (∑ i : Fin l.length, l[i.val]) = l.sum := by
    rw [← List.sum_ofFn,List.ofFn_getElem]
  have h2 : (∑ i : Fin l.length, l[i.val]^2) = (l.map (fun x => x^2)).sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map l (fun x : ℝ => x^2))
  rw [h1,h2] at h
  simpa using h

theorem inverse_root_sum_hasDerivAt (s : Multiset ℝ) (x : ℝ)
    (hx : ∀ r ∈ s, x ≠ r) :
    HasDerivAt (fun y : ℝ => (s.map (fun r => 1/(y-r))).sum)
      (-(s.map (fun r => (1/(x-r))^2)).sum) x := by
  induction s using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const x (0:ℝ)
  | @cons r s ih =>
      have hxr : x-r ≠ 0 := sub_ne_zero.mpr (hx r (by simp))
      have hs := ih (fun a ha => hx a (by simp [ha]))
      have hr := ((hasDerivAt_id x).sub_const r).inv hxr
      convert hr.fun_add hs using 1 <;> first | rfl |
        simp [Multiset.map_cons,Multiset.sum_cons,one_div,neg_add_rev,
          Pi.inv_apply,neg_div,add_comm]

/-- The degree-sharp Laguerre inequality for every real-rooted polynomial.
The evaluation point may itself be a repeated root. -/
theorem real_splits_laguerre {p : ℝ[X]} (hp : p.Splits)
    (hn : 1 ≤ p.natDegree) (x : ℝ) :
    (p.natDegree:ℝ)*p.eval x*p.derivative.derivative.eval x ≤
      ((p.natDegree:ℝ)-1)*(p.derivative.eval x)^2 := by
  by_cases hx : p.eval x = 0
  · have hnR : (1:ℝ) ≤ p.natDegree := by exact_mod_cast hn
    rw [hx,mul_zero,zero_mul]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  · have hroots : ∀ r ∈ p.roots, x ≠ r := by
      intro r hr hxr
      apply hx
      rw [hxr]
      exact Polynomial.isRoot_of_mem_roots hr
    have hsum := inverse_root_sum_hasDerivAt p.roots x hroots
    have hquot := (p.derivative.hasDerivAt x).div (p.hasDerivAt x) hx
    have hevent : (fun y : ℝ => p.derivative.eval y / p.eval y) =ᶠ[𝓝 x]
        (fun y : ℝ => (p.roots.map (fun r => 1/(y-r))).sum) := by
      filter_upwards [p.continuous.continuousAt.eventually_ne hx] with y hy
      exact hp.eval_derivative_div_eval_of_ne_zero hy
    have hderiv := hquot.unique (hsum.congr_of_eventuallyEq hevent)
    have hfirst := hp.eval_derivative_eq_eval_mul_sum hx
    let S := (p.roots.map (fun r => 1/(x-r))).sum
    let T := (p.roots.map (fun r => (1/(x-r))^2)).sum
    change (p.derivative.derivative.eval x*p.eval x-
      p.derivative.eval x*p.derivative.eval x)/(p.eval x)^2 = -T at hderiv
    have heq := (div_eq_iff (pow_ne_zero 2 hx)).mp hderiv
    have hcs := multiset_sq_sum_le_card_mul_sum_sq (p.roots.map (fun r => 1/(x-r)))
    simp only [Multiset.card_map,Multiset.map_map,Function.comp_def,
      ← hp.natDegree_eq_card_roots] at hcs
    change S^2 ≤ (p.natDegree:ℝ)*T at hcs
    change p.derivative.eval x = p.eval x*S at hfirst
    have hbound : (p.derivative.eval x)^2 ≤ (p.natDegree:ℝ)*T*(p.eval x)^2 := by
      rw [hfirst,mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hcs (sq_nonneg (p.eval x))]
    nlinarith [congrArg (fun z : ℝ => (p.natDegree:ℝ)*z) heq]

end DittertRybin
