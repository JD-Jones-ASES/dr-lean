import DR.Endpoint.LeadingBounds
import DR.Square.Stationarity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact leading-gauge algebra under independent row scaling

A fixed normalized nonidentical row law `X` is retained while its row
masses vary. Zero cells and zero columns remain zero under this variation.
The polynomial identities are signed and do not assume stationarity.
-/
namespace DittertRybin
open scoped BigOperators
open Certificates

/-- Vary the row masses without changing each row's column law. -/
def endpointRowBoard {m n : ℕ} (r : Fin m → ℝ) (X : Board m n) : Board m n :=
  fun i j => r i*X i j

theorem rowSum_endpointRowBoard {m n : ℕ} (r : Fin m → ℝ) (X : Board m n)
    (hs : ∀ i,rowSum X i=1) : rowSum (endpointRowBoard r X)=r := by
  funext i
  simp [rowSum,endpointRowBoard,← Finset.mul_sum,show ∑ j,X i j=1 from hs i]

theorem totalMass_endpointRowBoard {m n : ℕ} (r : Fin m → ℝ) (X : Board m n)
    (hs : ∀ i,rowSum X i=1) : totalMass (endpointRowBoard r X)=∑ i,r i := by
  simp only [totalMass,rowSum_endpointRowBoard r X hs]

/-- The collision term is formed from the actual fixed row law. -/
noncomputable def endpointLeadingColumnCollision {m n : ℕ} (X : Board m n) (j : Fin n) : ℝ :=
  (∑ i,X i j)^2-∑ i,X i j^2

/-- The signed polynomial whose square root is the column cost. -/
theorem endpointLeadingColumn_polynomial {m n : ℕ} (r : Fin m → ℝ) (X : Board m n)
    (hs : ∀ i,rowSum X i=1) (j : Fin n) :
    quadraticValue (endpointLeadingKernel (rowSum (endpointRowBoard r X)))
      (fun i => endpointRowBoard r X i j)=
        (∑ i,r i*X i j)^2-endpointLeadingScale r*endpointLeadingColumnCollision X j := by
  rw [rowSum_endpointRowBoard r X hs]
  change quadraticValue (endpointLeadingKernel r) (fun i => r i*X i j)=_
  rw [endpointLeadingKernel_scaled_quadratic]
  unfold endpointLeadingColumnCollision
  ring

/-- A nonzero-row product differentiated along an arbitrary real row direction. -/
theorem hasDerivAt_endpointLeadingScale_line {m : ℕ} (r w : Fin m → ℝ)
    (hr : ∀ i,r i≠0) :
    HasDerivAt (fun t : ℝ => endpointLeadingScale (fun i => r i+t*w i))
      (endpointLeadingScale r*∑ i,w i/r i) 0 := by
  have h := hasDerivAt_product_of_ne_zero (fun i t => r i+t*w i) w 0
    (fun i => by simpa using ((hasDerivAt_id (0:ℝ)).mul_const (w i)).const_add (r i))
    (fun i => by simpa using hr i)
  have hmul := h.const_mul ((m-2).factorial:ℝ)
  simpa only [endpointLeadingScale,zero_mul,add_zero,mul_assoc] using hmul

/-- Literal derivative of the actual column polynomial. No constrained
minimum or derivative condition is a premise of this identity. -/
theorem hasDerivAt_endpointLeadingColumn_polynomial {m n : ℕ}
    (r w : Fin m → ℝ) (X : Board m n) (hs : ∀ i,rowSum X i=1)
    (hr : ∀ i,r i≠0) (j : Fin n) :
    HasDerivAt (fun t : ℝ =>
      quadraticValue (endpointLeadingKernel (rowSum (endpointRowBoard (fun i => r i+t*w i) X)))
        (fun i => endpointRowBoard (fun i => r i+t*w i) X i j))
      (2*(∑ i,r i*X i j)*(∑ i,w i*X i j)-
        endpointLeadingScale r*endpointLeadingColumnCollision X j*(∑ i,w i/r i)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => ∑ i,(r i+t*w i)*X i j)
      (∑ i,w i*X i j) 0 := by
    simpa only [one_mul,id_eq] using HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ =>
      (((hasDerivAt_id (0:ℝ)).mul_const (w i)).const_add (r i)).mul_const (X i j))
  have h := (hc.pow 2).sub ((hasDerivAt_endpointLeadingScale_line r w hr).mul_const
    (endpointLeadingColumnCollision X j))
  convert! h using 1
  · funext t
    exact endpointLeadingColumn_polynomial (fun i => r i+t*w i) X hs j
  · simp only [zero_mul,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring


/-- Differentiation of a genuinely nonzero column cost. Empty columns
will instead be handled by their identically zero row-scaling function. -/
theorem hasDerivAt_endpointLeadingColumnCost {m n : ℕ}
    (r w : Fin m → ℝ) (X : Board m n) (hs : ∀ i,rowSum X i=1)
    (hr : ∀ i,r i≠0) (j : Fin n)
    (hq : 0<quadraticValue (endpointLeadingKernel r) (fun i => r i*X i j)) :
    HasDerivAt (fun t : ℝ => endpointLeadingColumnCost (endpointRowBoard (fun i => r i+t*w i) X) j)
      ((2*(∑ i,r i*X i j)*(∑ i,w i*X i j)-
        endpointLeadingScale r*endpointLeadingColumnCollision X j*(∑ i,w i/r i))/
          (2*endpointLeadingColumnCost (endpointRowBoard r X) j)) 0 := by
  have h := hasDerivAt_endpointLeadingColumn_polynomial r w X hs hr j
  have hq' : (quadraticValue
      (endpointLeadingKernel (rowSum (endpointRowBoard (fun i => r i+0*w i) X)))
      (fun i => endpointRowBoard (fun i => r i+0*w i) X i j))≠0 := by
    simpa only [zero_mul,add_zero,rowSum_endpointRowBoard r X hs,endpointRowBoard] using hq.ne'
  have hd := h.sqrt hq'
  simpa only [endpointLeadingColumnCost,zero_mul,add_zero] using hd

/-- Empty columns remain identically empty for every real row scaling. -/
theorem endpointLeadingColumnCost_zero_column {m n : ℕ} (r : Fin m → ℝ)
    (X : Board m n) (j : Fin n) (hj : ∀ i,X i j=0) :
    endpointLeadingColumnCost (endpointRowBoard r X) j=0 := by
  simp [endpointLeadingColumnCost,endpointRowBoard,hj,quadraticValue]

end DittertRybin
