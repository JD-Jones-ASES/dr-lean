import DR.Endpoint.ConsecutiveCutShared
import DR.Endpoint.BoundaryPermanent

/-! Formula-defined exact rational certificates for the finite consecutive
active cuts. Cast lemmas tie every numerical expression to the actual real
coefficient and permanent floor; the finite gates are separate modules. -/

namespace DittertRybin.Certificates

def consecutiveGammaRat (n : ℕ) : ℚ := (n.factorial : ℚ)/(n : ℚ)^n
def consecutiveAvoidanceRat (m n : ℕ) : ℚ := (n.descFactorial m : ℚ)/(n : ℚ)^m
def consecutiveBoundaryRat (n : ℕ) : ℚ :=
  ((n-2).factorial : ℚ)*(((n : ℚ)-2)/((n : ℚ)-1)^2)^(n-2)

def consecutiveRowCutRat (m k : ℕ) : ℚ :=
  2*(101/100 : ℚ)^2*(k : ℚ)*((m : ℚ)-k)/(m : ℚ)^3
def consecutiveColumnCutRat (m n l : ℕ) : ℚ :=
  2*((n : ℚ)-1)*(l : ℚ)*((n : ℚ)-l)/((n : ℚ)^2*m)
def consecutiveDemandRat (m n k l : ℕ) : ℚ := (k : ℚ)/m+(l : ℚ)/n-1
def consecutiveCutRat (m n k l : ℕ) : ℚ :=
  (consecutiveRowCutRat m k +
    (consecutiveGammaRat m/consecutiveAvoidanceRat m n)*consecutiveColumnCutRat m n l) /
    (consecutiveDemandRat m n k l)^2

def consecutiveRectangleRat (m n k l : ℕ) : ℚ :=
  consecutiveGammaRat (n-m+k)*consecutiveGammaRat l/consecutiveGammaRat (k+l-m)
def consecutiveRookFloorRat (m n k l : ℕ) : ℚ :=
  consecutiveAvoidanceRat m n *
    (if k < m ∧ l < n then max (consecutiveBoundaryRat n) (consecutiveRectangleRat m n k l)
      else consecutiveBoundaryRat n) / consecutiveGammaRat n

/-- Only non-whole positive cuts need a numerical minimum-dilation certificate. -/
def ConsecutiveCutCertificate (m k l : ℕ) : Prop :=
  let n := m+1
  let b := consecutiveAvoidanceRat m n
  let C := consecutiveCutRat m n k l
  let beta := consecutiveRookFloorRat m n k l
  0 < consecutiveDemandRat m n k l → (k ≠ m ∨ l ≠ n) →
    C*b/(1-b) < 1/500 ∧ beta-b-(m : ℚ)^2*C*beta^2/(4*(1-b)) > b/2000

instance (m k l : ℕ) : Decidable (ConsecutiveCutCertificate m k l) := by
  unfold ConsecutiveCutCertificate
  infer_instance

@[simp] theorem consecutiveGammaRat_cast (n : ℕ) :
    (consecutiveGammaRat n : ℝ) = dittertConstant n := by
  simp [consecutiveGammaRat, dittertConstant]
@[simp] theorem consecutiveAvoidanceRat_cast (m n : ℕ) :
    (consecutiveAvoidanceRat m n : ℝ) = distinctUniformProbability n m := by
  simp [consecutiveAvoidanceRat, distinctUniformProbability]
@[simp] theorem consecutiveBoundaryRat_cast (n : ℕ) :
    (consecutiveBoundaryRat n : ℝ) = boundaryPermanentFloor n := by
  simp [consecutiveBoundaryRat, boundaryPermanentFloor]
@[simp] theorem consecutiveRowCutRat_cast (m k : ℕ) :
    (consecutiveRowCutRat m k : ℝ) = endpointSizedRowCutCoefficient (101/100) m k := by
  simp [consecutiveRowCutRat, endpointSizedRowCutCoefficient]
@[simp] theorem consecutiveColumnCutRat_cast (m n l : ℕ) :
    (consecutiveColumnCutRat m n l : ℝ) = endpointSizedColumnCutCoefficient m n l := by
  simp [consecutiveColumnCutRat, endpointSizedColumnCutCoefficient]
@[simp] theorem consecutiveDemandRat_cast (m n k l : ℕ) :
    (consecutiveDemandRat m n k l : ℝ) = (k : ℝ)/m+(l : ℝ)/n-1 := by
  simp [consecutiveDemandRat]
@[simp] theorem consecutiveCutRat_cast (m n k l : ℕ) :
    (consecutiveCutRat m n k l : ℝ) = endpointSizedCutCoefficient (101/100) m n k l := by
  simp [consecutiveCutRat, endpointSizedCutCoefficient]
@[simp] theorem consecutiveRectangleRat_cast (m n k l : ℕ) :
    (consecutiveRectangleRat m n k l : ℝ) =
      dittertConstant (n-m+k)*dittertConstant l/dittertConstant (k+l-m) := by
  simp [consecutiveRectangleRat]

end DittertRybin.Certificates
