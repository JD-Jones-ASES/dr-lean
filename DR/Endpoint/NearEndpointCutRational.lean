import DR.Endpoint.NearEndpointCutFloors

/-! Formula-defined rational gates for the five finite near-endpoint cases.
The literal cubic brackets and excesses are mathematical certificate data
for dimensions 21 through 25. No permanent lower bound is
assumed from the data alone: its matrix interpretation is a separate step. -/
namespace DittertRybin.Certificates

def nearEndpointGammaRat (n : ℕ) : ℚ := (n.factorial : ℚ)/(n : ℚ)^n
def nearEndpointAvoidanceRat (n : ℕ) : ℚ := (n.descFactorial (n-1) : ℚ)/(n : ℚ)^(n-1)
def nearEndpointBoundaryRat (n : ℕ) : ℚ :=
  ((n-2).factorial : ℚ)*(((n : ℚ)-2)/((n : ℚ)-1)^2)^(n-2)

def nearEndpointRootLeft (n : ℕ) : ℚ :=
  (match n with
    | 21 => 4976889
    | 22 => 4741862
    | 23 => 4527961
    | 24 => 4332468
    | 25 => 4153110
    | _ => 0)/100000000

def nearEndpointRootRight (n : ℕ) : ℚ := nearEndpointRootLeft n+1/100000000

def nearEndpointExcessRat (n : ℕ) : ℚ :=
  (match n with
    | 21 => 1112507
    | 22 => 1014678
    | 23 => 929196
    | 24 => 854069
    | 25 => 787692
    | _ => 0)/1000000000

def nearEndpointCubicRat (m : ℕ) (u : ℚ) : ℚ :=
  ((m : ℚ)^2+3*m+4)*u^3-((m : ℚ)^2+3*m+8)*u^2+((m : ℚ)^2+m+4)*u-m

def nearEndpointTwoZeroXRat (m : ℕ) (u : ℚ) : ℚ := ((m : ℚ)-2+2*u)/(m : ℚ)^2

def nearEndpointTwoZeroHRat (m : ℕ) (u : ℚ) : ℚ :=
  let x := nearEndpointTwoZeroXRat m u
  let a := (1-u)/(m : ℚ)
  x^2*u^2+2*m*x*a^2*u+(m : ℚ)*((m : ℚ)-1)*a^4

def nearEndpointPermanentFloorRat (n : ℕ) : ℚ :=
  nearEndpointBoundaryRat (n+1)*(1+nearEndpointExcessRat n)

def NearEndpointBracketCertificate (n : ℕ) : Prop :=
  let m := n-1
  let lo := nearEndpointRootLeft n
  let hi := nearEndpointRootRight n
  0<lo ∧ lo<hi ∧ hi<1/(m : ℚ) ∧
    nearEndpointCubicRat m lo<0 ∧ 0<nearEndpointCubicRat m hi ∧
    0<nearEndpointExcessRat n ∧
    nearEndpointPermanentFloorRat n <
      (m.factorial : ℚ)*(nearEndpointTwoZeroXRat m lo)^(m-2)*nearEndpointTwoZeroHRat m hi

instance (n : ℕ) : Decidable (NearEndpointBracketCertificate n) := by
  unfold NearEndpointBracketCertificate
  infer_instance

def nearEndpointCutRat (n k l : ℕ) : ℚ :=
  2*((k : ℚ)*((n : ℚ)-k)+(l : ℚ)*((n : ℚ)-l))/((k : ℚ)+l-n)^2

def nearEndpointRectangleRat (n k l : ℕ) : ℚ :=
  nearEndpointGammaRat (k+1)*nearEndpointGammaRat (l+1)/nearEndpointGammaRat (k+l+1-n)

def nearEndpointCutRookFloorRat (n k l : ℕ) : ℚ :=
  nearEndpointAvoidanceRat n*
    (if k<n ∧ l<n then max (nearEndpointPermanentFloorRat n) (nearEndpointRectangleRat n k l)
      else nearEndpointPermanentFloorRat n)/nearEndpointBoundaryRat (n+1)

def NearEndpointCutCertificate (n k l : ℕ) : Prop :=
  let a := nearEndpointAvoidanceRat n
  let C := nearEndpointCutRat n k l
  let beta := nearEndpointCutRookFloorRat n k l
  n<k+l → (k≠n ∨ l≠n) →
    C*a/(1-a)<1/10000 ∧ beta-a-((n-1 : ℕ) : ℚ)^2*C*beta^2/(4*(1-a))>3*a/10000

instance (n k l : ℕ) : Decidable (NearEndpointCutCertificate n k l) := by
  unfold NearEndpointCutCertificate
  infer_instance

@[simp] theorem nearEndpointGammaRat_cast (n : ℕ) :
    (nearEndpointGammaRat n : ℝ)=dittertConstant n := by
  simp [nearEndpointGammaRat,dittertConstant]
@[simp] theorem nearEndpointAvoidanceRat_cast (n : ℕ) :
    (nearEndpointAvoidanceRat n : ℝ)=distinctUniformProbability n (n-1) := by
  simp [nearEndpointAvoidanceRat,distinctUniformProbability]
@[simp] theorem nearEndpointBoundaryRat_cast (n : ℕ) :
    (nearEndpointBoundaryRat n : ℝ)=boundaryPermanentFloor n := by
  simp [nearEndpointBoundaryRat,boundaryPermanentFloor]
@[simp] theorem nearEndpointCutRat_cast (n k l : ℕ) :
    (nearEndpointCutRat n k l : ℝ)=nearEndpointSizedCutCoefficient n k l := by
  simp [nearEndpointCutRat,nearEndpointSizedCutCoefficient]
@[simp] theorem nearEndpointRectangleRat_cast (n k l : ℕ) :
    (nearEndpointRectangleRat n k l : ℝ)=nearEndpointRectangleFloor n k l := by
  simp [nearEndpointRectangleRat,nearEndpointRectangleFloor]
@[simp] theorem nearEndpointCutRookFloorRat_cast (n k l : ℕ) :
    (nearEndpointCutRookFloorRat n k l : ℝ)=
      nearEndpointCutRookFloor n (nearEndpointPermanentFloorRat n : ℝ) k l := by
  by_cases h : k<n ∧ l<n <;> simp [nearEndpointCutRookFloorRat,nearEndpointCutRookFloor,h]

end DittertRybin.Certificates
