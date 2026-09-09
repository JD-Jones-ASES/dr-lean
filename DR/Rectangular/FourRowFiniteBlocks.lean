import DR.Rectangular.FourRowFiniteParameter
import DR.Rectangular.FourRowFiniteRole

/-!
# Literal reduced entries and denominator clearing

The row/column averages retain their actual multiplicities. This module
identifies the denominator-cleared expressions for the four two-axis
sectors. It proves neither a finite matrix gate nor the physical decomposition;
those independent obligations use these exact entries.
-/

namespace DittertRybin
open scoped BigOperators
noncomputable section

/-- Averaging two ordinary labels: one equal choice and `count-1` unequal choices. -/
def fourRowFiniteOrdinaryAverage (first : ℕ) (count : ℝ)
    (f : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = first ∧ j = first then
    (f first first + (count-1)*f first (first+1))/count
  else f i j

theorem fourRowFiniteOrdinaryAverage_smul (first : ℕ) (count d : ℝ)
    (f : ℕ → ℕ → ℝ) (i j : ℕ) :
    fourRowFiniteOrdinaryAverage first count (fun i j => d*f i j) i j =
      d*fourRowFiniteOrdinaryAverage first count f i j := by
  unfold fourRowFiniteOrdinaryAverage
  split_ifs <;> ring

theorem fourRowFiniteOrdinaryAverage_clear (first : ℕ) (count d : ℝ)
    (hc : count ≠ 0) (f : ℕ → ℕ → ℝ) (i j : ℕ) :
    d*fourRowFiniteOrdinaryAverage first count f i j =
      if i = first ∧ j = first then
        (d/count)*f first first + (d-d/count)*f first (first+1)
      else d*f i j := by
  unfold fourRowFiniteOrdinaryAverage
  split_ifs
  · field_simp
  · rfl

theorem fourRowFiniteOrdinaryCount_parameter_pos {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (q : Fin 3) :
    0 < (a : ℝ)/u - ((q : ℕ)+1 : ℝ) := by
  have hq : ((q : ℕ)+1 : ℝ) ≤ 3 := by exact_mod_cast (show (q : ℕ)+1 ≤ 3 by omega)
  have hq0 : (0 : ℝ) ≤ ((q : ℕ)+1 : ℝ) := by positivity
  have ham : (5 : ℝ) ≤ a := by exact_mod_cast ha
  have hmul : ((q : ℕ)+1 : ℝ)*u ≤ 3 :=
    (mul_le_of_le_one_right hq0 hu1).trans hq
  exact sub_pos.mpr ((lt_div_iff₀ hu).mpr (by linarith))

/-- The polynomial expression for `D/(a/u-(q+1))`, with no ordinary-column denominator. -/
def fourRowFiniteColumnClearing (a : ℕ) (u : ℝ) (q : Fin 3) : ℝ :=
  (u/a) * ∏ s ∈ Finset.univ.erase q, (1-((s : ℕ)+1 : ℝ)*u/a)

theorem fourRowFiniteColumnClearing_eq {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (q : Fin 3) :
    fourRowFiniteDenominator a u / ((a : ℝ)/u-((q : ℕ)+1 : ℝ)) =
      fourRowFiniteColumnClearing a u q := by
  simpa only [fourRowFiniteColumnClearing] using
    fourRowFiniteDenominator_cancel (show (5 : ℝ) ≤ a by exact_mod_cast ha) hu hu1 q

def fourRowFiniteClearedColumnAverage (a : ℕ) (u : ℝ) (q : Fin 3)
    (f : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = (q : ℕ)+1 ∧ j = (q : ℕ)+1 then
    fourRowFiniteColumnClearing a u q * f ((q : ℕ)+1) ((q : ℕ)+1) +
      (fourRowFiniteDenominator a u-fourRowFiniteColumnClearing a u q) *
        f ((q : ℕ)+1) ((q : ℕ)+2)
  else fourRowFiniteDenominator a u*f i j

theorem fourRowFiniteClearedColumnAverage_eq {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (q : Fin 3)
    (f : ℕ → ℕ → ℝ) (i j : ℕ) :
    fourRowFiniteDenominator a u *
      fourRowFiniteOrdinaryAverage ((q : ℕ)+1) ((a : ℝ)/u-((q : ℕ)+1 : ℝ)) f i j =
      fourRowFiniteClearedColumnAverage a u q f i j := by
  rw [fourRowFiniteOrdinaryAverage_clear _ _ _
    (fourRowFiniteOrdinaryCount_parameter_pos ha hu hu1 q).ne',
    fourRowFiniteColumnClearing_eq ha hu hu1]
  rfl

def fourRowFiniteRealRoleEntry (h : ℕ → ℝ) (mark : List (ℕ × ℕ))
    (x y : ℕ × ℕ) : ℝ := h (fourRowFiniteCanonicalRoleKey mark x y)

def fourRowFiniteTrivialEntry (nr nc : ℕ) (n : ℝ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) : ℝ :=
  fourRowFiniteOrdinaryAverage nr (4-nr)
    (fun i k => fourRowFiniteOrdinaryAverage nc (n-nc)
      (fun j l => fourRowFiniteRealRoleEntry h mark (i,j) (k,l)) x.2 y.2) x.1 y.1

def fourRowFiniteRowStandardEntry (nr nc : ℕ) (n : ℝ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) (j l : ℕ) : ℝ :=
  fourRowFiniteOrdinaryAverage nc (n-nc)
    (fun k t => fourRowFiniteRealRoleEntry h mark (nr,k) (nr,t) -
      fourRowFiniteRealRoleEntry h mark (nr,k) (nr+1,t)) j l

def fourRowFiniteColumnStandardEntry (nr nc : ℕ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) (i k : ℕ) : ℝ :=
  fourRowFiniteOrdinaryAverage nr (4-nr)
    (fun j l => fourRowFiniteRealRoleEntry h mark (j,nc) (l,nc) -
      fourRowFiniteRealRoleEntry h mark (j,nc) (l,nc+1)) i k

def fourRowFiniteInteractionEntry (nr nc : ℕ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) : ℝ :=
  fourRowFiniteRealRoleEntry h mark (nr,nc) (nr,nc) -
    fourRowFiniteRealRoleEntry h mark (nr,nc) (nr+1,nc) -
    fourRowFiniteRealRoleEntry h mark (nr,nc) (nr,nc+1) +
    fourRowFiniteRealRoleEntry h mark (nr,nc) (nr+1,nc+1)

theorem fourRowFiniteTrivialEntry_clear {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (nr : ℕ) (q : Fin 3)
    (h : ℕ → ℝ) (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) :
    fourRowFiniteDenominator a u *
      fourRowFiniteTrivialEntry nr ((q : ℕ)+1) ((a : ℝ)/u) h mark x y =
      fourRowFiniteOrdinaryAverage nr (4-nr)
        (fun i k => fourRowFiniteClearedColumnAverage a u q
          (fun j l => fourRowFiniteRealRoleEntry h mark (i,j) (k,l)) x.2 y.2) x.1 y.1 := by
  unfold fourRowFiniteTrivialEntry
  rw [← fourRowFiniteOrdinaryAverage_smul]
  congr 1
  funext i k
  simpa only [Nat.cast_add, Nat.cast_one] using
    fourRowFiniteClearedColumnAverage_eq ha hu hu1 q
      (fun j l => fourRowFiniteRealRoleEntry h mark (i,j) (k,l)) x.2 y.2

theorem fourRowFiniteRowStandardEntry_clear {a : ℕ} (ha : 5 ≤ a)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (nr : ℕ) (q : Fin 3)
    (h : ℕ → ℝ) (mark : List (ℕ × ℕ)) (j l : ℕ) :
    fourRowFiniteDenominator a u *
      fourRowFiniteRowStandardEntry nr ((q : ℕ)+1) ((a : ℝ)/u) h mark j l =
      fourRowFiniteClearedColumnAverage a u q
        (fun k t => fourRowFiniteRealRoleEntry h mark (nr,k) (nr,t) -
          fourRowFiniteRealRoleEntry h mark (nr,k) (nr+1,t)) j l := by
  simpa only [fourRowFiniteRowStandardEntry, Nat.cast_add, Nat.cast_one] using
    fourRowFiniteClearedColumnAverage_eq ha hu hu1 q
      (fun k t => fourRowFiniteRealRoleEntry h mark (nr,k) (nr,t) -
        fourRowFiniteRealRoleEntry h mark (nr,k) (nr+1,t)) j l

end
end DittertRybin
