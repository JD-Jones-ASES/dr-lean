import DR.Rectangular.FourRowFiniteBlocks

/-!
# The actual cleared univariate block polynomials

These expressions are built directly from the role polynomials and the
literal ordinary-label averages. Their evaluations equal the actual cleared
entries, for every admissible parameter. Stored coefficient tables must be
proved equal to these polynomials before their positivity gates are used.
-/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial Certificates
noncomputable section

abbrev FourRowFiniteUnivariate := MvPolynomial (Fin 1) ℚ

def fourRowFinitePolynomialDenominator (a : ℕ) : FourRowFiniteUnivariate :=
  ∏ q : Fin 3, (1-C (((q : ℕ)+1 : ℚ)/a)*X 0)

def fourRowFinitePolynomialColumnClearing (a : ℕ) (q : Fin 3) : FourRowFiniteUnivariate :=
  C (1/(a : ℚ))*X 0 *
    ∏ s ∈ Finset.univ.erase q, (1-C (((s : ℕ)+1 : ℚ)/a)*X 0)

def fourRowFinitePolynomialAverage (first : ℕ) (count : ℚ)
    (f : ℕ → ℕ → FourRowFiniteUnivariate) (i j : ℕ) : FourRowFiniteUnivariate :=
  if i = first ∧ j = first then
    C (1/count)*f first first + C ((count-1)/count)*f first (first+1)
  else f i j

def fourRowFinitePolynomialColumnAverage (a : ℕ) (q : Fin 3)
    (f : ℕ → ℕ → FourRowFiniteUnivariate) (i j : ℕ) : FourRowFiniteUnivariate :=
  if i = (q : ℕ)+1 ∧ j = (q : ℕ)+1 then
    fourRowFinitePolynomialColumnClearing a q*f ((q : ℕ)+1) ((q : ℕ)+1) +
      (fourRowFinitePolynomialDenominator a-fourRowFinitePolynomialColumnClearing a q)*
        f ((q : ℕ)+1) ((q : ℕ)+2)
  else fourRowFinitePolynomialDenominator a*f i j

theorem fourRowFinitePolynomialDenominator_eval (a : ℕ) (u : ℝ) :
    rationalEval (fun _ => u) (fourRowFinitePolynomialDenominator a) =
      fourRowFiniteDenominator a u := by
  simp only [rationalEval, fourRowFinitePolynomialDenominator, eval₂_prod, eval₂_sub,
    eval₂_one, eval₂_mul, eval₂_C, eval₂_X]
  unfold fourRowFiniteDenominator
  apply Finset.prod_congr rfl
  intro q _
  simp only [Rat.coe_castHom]
  push_cast
  ring

theorem fourRowFinitePolynomialColumnClearing_eval (a : ℕ) (u : ℝ) (q : Fin 3) :
    rationalEval (fun _ => u) (fourRowFinitePolynomialColumnClearing a q) =
      fourRowFiniteColumnClearing a u q := by
  simp only [rationalEval, fourRowFinitePolynomialColumnClearing, eval₂_prod, eval₂_sub,
    eval₂_one, eval₂_mul, eval₂_C, eval₂_X]
  unfold fourRowFiniteColumnClearing
  have he : ((Rat.castHom ℝ) (1/(a : ℚ)))*u = u/a := by
    simp only [Rat.coe_castHom]
    push_cast
    ring
  rw [he]
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  simp only [Rat.coe_castHom]
  push_cast
  ring

theorem fourRowFinitePolynomialAverage_eval (first : ℕ) (count : ℚ)
    (f : ℕ → ℕ → FourRowFiniteUnivariate) (i j : ℕ) (u : ℝ) :
    rationalEval (fun _ => u) (fourRowFinitePolynomialAverage first count f i j) =
      fourRowFiniteOrdinaryAverage first count (fun i j => rationalEval (fun _ => u) (f i j)) i j := by
  unfold fourRowFinitePolynomialAverage fourRowFiniteOrdinaryAverage
  split_ifs
  · simp only [rationalEval, eval₂_add, eval₂_mul, eval₂_C]
    simp only [Rat.coe_castHom]
    push_cast
    ring
  · rfl

theorem fourRowFinitePolynomialColumnAverage_eval (a : ℕ) (q : Fin 3)
    (f : ℕ → ℕ → FourRowFiniteUnivariate) (i j : ℕ) (u : ℝ) :
    rationalEval (fun _ => u) (fourRowFinitePolynomialColumnAverage a q f i j) =
      fourRowFiniteClearedColumnAverage a u q (fun i j => rationalEval (fun _ => u) (f i j)) i j := by
  unfold fourRowFinitePolynomialColumnAverage fourRowFiniteClearedColumnAverage
  split_ifs <;>
    simp only [rationalEval, eval₂_add, eval₂_sub, eval₂_mul]
  · rw [← fourRowFinitePolynomialDenominator_eval a u, ← fourRowFinitePolynomialColumnClearing_eval a u q]
    rfl
  · rw [← fourRowFinitePolynomialDenominator_eval a u]
    rfl

def fourRowFinitePolynomialRoleEntry (h : ℕ → FourRowFiniteUnivariate)
    (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) : FourRowFiniteUnivariate :=
  h (fourRowFiniteCanonicalRoleKey mark x y)

def fourRowFiniteTrivialPolynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) :
    FourRowFiniteUnivariate :=
  fourRowFinitePolynomialAverage nr (4-nr)
    (fun i k => fourRowFinitePolynomialColumnAverage a q
      (fun j l => fourRowFinitePolynomialRoleEntry h mark (i,j) (k,l)) x.2 y.2) x.1 y.1

def fourRowFiniteRowStandardPolynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) (j l : ℕ) :
    FourRowFiniteUnivariate :=
  fourRowFinitePolynomialColumnAverage a q
    (fun k t => fourRowFinitePolynomialRoleEntry h mark (nr,k) (nr,t) -
      fourRowFinitePolynomialRoleEntry h mark (nr,k) (nr+1,t)) j l

def fourRowFiniteColumnStandardPolynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) (i k : ℕ) :
    FourRowFiniteUnivariate :=
  fourRowFinitePolynomialDenominator a * fourRowFinitePolynomialAverage nr (4-nr)
    (fun j l => fourRowFinitePolynomialRoleEntry h mark (j,(q : ℕ)+1) (l,(q : ℕ)+1) -
      fourRowFinitePolynomialRoleEntry h mark (j,(q : ℕ)+1) (l,(q : ℕ)+2)) i k

def fourRowFiniteInteractionPolynomial (nr : ℕ) (q : Fin 3) (a : ℕ)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) : FourRowFiniteUnivariate :=
  fourRowFinitePolynomialDenominator a *
    (fourRowFinitePolynomialRoleEntry h mark (nr,(q : ℕ)+1) (nr,(q : ℕ)+1) -
      fourRowFinitePolynomialRoleEntry h mark (nr,(q : ℕ)+1) (nr+1,(q : ℕ)+1) -
      fourRowFinitePolynomialRoleEntry h mark (nr,(q : ℕ)+1) (nr,(q : ℕ)+2) +
      fourRowFinitePolynomialRoleEntry h mark (nr,(q : ℕ)+1) (nr+1,(q : ℕ)+2))

theorem fourRowFiniteTrivialPolynomial_eval {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (nr : ℕ) (q : Fin 3)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) :
    rationalEval (fun _ => u) (fourRowFiniteTrivialPolynomial nr q a h mark x y) =
      fourRowFiniteDenominator a u * fourRowFiniteTrivialEntry nr ((q : ℕ)+1) ((a : ℝ)/u)
        (fun key => rationalEval (fun _ => u) (h key)) mark x y := by
  rw [fourRowFiniteTrivialEntry_clear ha hu hu1]
  simp only [fourRowFiniteTrivialPolynomial, fourRowFinitePolynomialAverage_eval,
    fourRowFinitePolynomialColumnAverage_eval, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_natCast,
    fourRowFinitePolynomialRoleEntry, fourRowFiniteRealRoleEntry]

theorem fourRowFiniteRowStandardPolynomial_eval {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (nr : ℕ) (q : Fin 3)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) (j l : ℕ) :
    rationalEval (fun _ => u) (fourRowFiniteRowStandardPolynomial nr q a h mark j l) =
      fourRowFiniteDenominator a u * fourRowFiniteRowStandardEntry nr ((q : ℕ)+1) ((a : ℝ)/u)
        (fun key => rationalEval (fun _ => u) (h key)) mark j l := by
  rw [fourRowFiniteRowStandardEntry_clear ha hu hu1]
  rw [fourRowFiniteRowStandardPolynomial, fourRowFinitePolynomialColumnAverage_eval]
  simp only [fourRowFinitePolynomialRoleEntry, fourRowFiniteRealRoleEntry, rationalEval, eval₂_sub]

theorem fourRowFiniteColumnStandardPolynomial_eval (a : ℕ) (u : ℝ) (nr : ℕ) (q : Fin 3)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) (i k : ℕ) :
    rationalEval (fun _ => u) (fourRowFiniteColumnStandardPolynomial nr q a h mark i k) =
      fourRowFiniteDenominator a u * fourRowFiniteColumnStandardEntry nr ((q : ℕ)+1)
        (fun key => rationalEval (fun _ => u) (h key)) mark i k := by
  change rationalEval (fun _ => u) (fourRowFinitePolynomialDenominator a * _) = _
  simp only [rationalEval, eval₂_mul]
  change rationalEval (fun _ => u) (fourRowFinitePolynomialDenominator a) * _ = _
  rw [fourRowFinitePolynomialDenominator_eval]
  congr 1
  change rationalEval (fun _ => u) (fourRowFinitePolynomialAverage _ _ _ _ _) = _
  rw [fourRowFinitePolynomialAverage_eval]
  simp only [fourRowFiniteColumnStandardEntry, fourRowFinitePolynomialRoleEntry,
    fourRowFiniteRealRoleEntry, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_natCast, rationalEval, eval₂_sub]

theorem fourRowFiniteInteractionPolynomial_eval (a : ℕ) (u : ℝ) (nr : ℕ) (q : Fin 3)
    (h : ℕ → FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) :
    rationalEval (fun _ => u) (fourRowFiniteInteractionPolynomial nr q a h mark) =
      fourRowFiniteDenominator a u * fourRowFiniteInteractionEntry nr ((q : ℕ)+1)
        (fun key => rationalEval (fun _ => u) (h key)) mark := by
  simp only [fourRowFiniteInteractionPolynomial, rationalEval, eval₂_mul, eval₂_add, eval₂_sub]
  change rationalEval (fun _ => u) (fourRowFinitePolynomialDenominator a) * _ = _
  rw [fourRowFinitePolynomialDenominator_eval]
  rfl

end
end DittertRybin
