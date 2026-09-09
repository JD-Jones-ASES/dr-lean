import DR.Rectangular.FourRowFinitePowerAlgebra

/-! Exact finite coefficient vectors for all four actual cleared sectors. -/

namespace DittertRybin
open MvPolynomial Certificates
noncomputable section

def fourRowFinitePowerAverage {d : ℕ} (first : ℕ) (count : ℚ)
    (f : ℕ → ℕ → Fin (d+1) → ℚ) (i j : ℕ) (k : Fin (d+1)) : ℚ :=
  if i = first ∧ j = first then
    (1/count)*f first first k+((count-1)/count)*f first (first+1) k
  else f i j k

def fourRowFiniteColumnPower (a : ℕ) (q : Fin 3)
    (f : ℕ → ℕ → Fin 5 → ℚ) (i j : ℕ) (k : Fin 8) : ℚ :=
  if i = (q : ℕ)+1 ∧ j = (q : ℕ)+1 then
    fourRowFinitePowerProduct (fourRowFiniteColumnClearingPower a q)
      (f ((q : ℕ)+1) ((q : ℕ)+1)) k+
    fourRowFinitePowerProduct
      (fun d => fourRowFiniteDenominatorPower a d-fourRowFiniteColumnClearingPower a q d)
      (f ((q : ℕ)+1) ((q : ℕ)+2)) k
  else fourRowFinitePowerProduct (fourRowFiniteDenominatorPower a) (f i j) k

theorem fourRowFinitePowerAverage_polynomial {d : ℕ} (first : ℕ) (count : ℚ)
    (f : ℕ → ℕ → Fin (d+1) → ℚ) (i j : ℕ) :
    powerPolynomial (fourRowFinitePowerAverage first count f i j) =
      fourRowFinitePolynomialAverage first count (fun i j => powerPolynomial (f i j)) i j := by
  unfold fourRowFinitePowerAverage fourRowFinitePolynomialAverage
  split_ifs <;> simp only [fourRowFinitePower_add, fourRowFinitePower_scale]

theorem fourRowFiniteColumnPower_polynomial (a : ℕ) (q : Fin 3)
    (f : ℕ → ℕ → Fin 5 → ℚ) (i j : ℕ) :
    powerPolynomial (fourRowFiniteColumnPower a q f i j) =
      fourRowFinitePolynomialColumnAverage a q (fun i j => powerPolynomial (f i j)) i j := by
  unfold fourRowFiniteColumnPower fourRowFinitePolynomialColumnAverage
  split_ifs <;>
    simp only [fourRowFinitePower_add, fourRowFinitePowerProduct_polynomial,
      fourRowFinitePower_sub, fourRowFiniteDenominatorPower_polynomial,
      fourRowFiniteColumnClearingPower_polynomial]

def fourRowFiniteRolePower (h : ℕ → Fin 5 → ℚ)
    (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) : Fin 5 → ℚ :=
  h (fourRowFiniteCanonicalRoleKey mark x y)

def fourRowFiniteTrivialPower (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) : Fin 8 → ℚ :=
  fourRowFinitePowerAverage nr (4-nr)
    (fun i k => fourRowFiniteColumnPower a q
      (fun j l => fourRowFiniteRolePower h mark (i,j) (k,l)) x.2 y.2) x.1 y.1

def fourRowFiniteRowStandardPower (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) (j l : ℕ) : Fin 8 → ℚ :=
  fourRowFiniteColumnPower a q (fun k t d =>
    fourRowFiniteRolePower h mark (nr,k) (nr,t) d-
    fourRowFiniteRolePower h mark (nr,k) (nr+1,t) d) j l

def fourRowFiniteColumnStandardPower (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) (i k : ℕ) : Fin 8 → ℚ :=
  fourRowFinitePowerProduct (fourRowFiniteDenominatorPower a)
    (fourRowFinitePowerAverage nr (4-nr) (fun j l d =>
      fourRowFiniteRolePower h mark (j,(q : ℕ)+1) (l,(q : ℕ)+1) d-
      fourRowFiniteRolePower h mark (j,(q : ℕ)+1) (l,(q : ℕ)+2) d) i k)

def fourRowFiniteInteractionPower (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) : Fin 8 → ℚ :=
  fourRowFinitePowerProduct (fourRowFiniteDenominatorPower a) (fun d =>
    fourRowFiniteRolePower h mark (nr,(q : ℕ)+1) (nr,(q : ℕ)+1) d-
    fourRowFiniteRolePower h mark (nr,(q : ℕ)+1) (nr+1,(q : ℕ)+1) d-
    fourRowFiniteRolePower h mark (nr,(q : ℕ)+1) (nr,(q : ℕ)+2) d+
    fourRowFiniteRolePower h mark (nr,(q : ℕ)+1) (nr+1,(q : ℕ)+2) d)

theorem fourRowFiniteTrivialPower_polynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) :
    powerPolynomial (fourRowFiniteTrivialPower nr q a h mark x y) =
      fourRowFiniteTrivialPolynomial nr q a (fun key => powerPolynomial (h key)) mark x y := by
  simp only [fourRowFiniteTrivialPower, fourRowFiniteTrivialPolynomial,
    fourRowFinitePowerAverage_polynomial, fourRowFiniteColumnPower_polynomial,
    fourRowFiniteRolePower, fourRowFinitePolynomialRoleEntry]

theorem fourRowFiniteRowStandardPower_polynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) (j l : ℕ) :
    powerPolynomial (fourRowFiniteRowStandardPower nr q a h mark j l) =
      fourRowFiniteRowStandardPolynomial nr q a (fun key => powerPolynomial (h key)) mark j l := by
  simp only [fourRowFiniteRowStandardPower, fourRowFiniteRowStandardPolynomial,
    fourRowFiniteColumnPower_polynomial, fourRowFinitePower_sub,
    fourRowFiniteRolePower, fourRowFinitePolynomialRoleEntry]

theorem fourRowFiniteColumnStandardPower_polynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) (i k : ℕ) :
    powerPolynomial (fourRowFiniteColumnStandardPower nr q a h mark i k) =
      fourRowFiniteColumnStandardPolynomial nr q a (fun key => powerPolynomial (h key)) mark i k := by
  simp only [fourRowFiniteColumnStandardPower, fourRowFiniteColumnStandardPolynomial,
    fourRowFinitePowerProduct_polynomial, fourRowFinitePowerAverage_polynomial,
    fourRowFiniteDenominatorPower_polynomial, fourRowFinitePower_sub,
    fourRowFiniteRolePower, fourRowFinitePolynomialRoleEntry]

theorem fourRowFiniteInteractionPower_polynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → Fin 5 → ℚ) (mark : List (ℕ × ℕ)) :
    powerPolynomial (fourRowFiniteInteractionPower nr q a h mark) =
      fourRowFiniteInteractionPolynomial nr q a (fun key => powerPolynomial (h key)) mark := by
  simp only [fourRowFiniteInteractionPower, fourRowFiniteInteractionPolynomial,
    fourRowFinitePowerProduct_polynomial, fourRowFinitePower_add, fourRowFinitePower_sub,
    fourRowFiniteDenominatorPower_polynomial, fourRowFiniteRolePower, fourRowFinitePolynomialRoleEntry]

end
end DittertRybin
