import DR.Endpoint.RectangularTransport
import Mathlib.Data.Nat.GCD.Basic

/-! A positive rectangular cut has an integer numerator divisible by every
common divisor of the dimensions. This proves the arithmetic grid bound;
no attainment of the grid minimum is asserted. -/
namespace DittertRybin

/-- Positive cut demand is at least a common divisor divided by mn. The
cardinal inputs may be any natural numbers; no finite census is used. -/
theorem positive_rectangular_cut_grid {m n g k l : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hgm : g ∣ m) (hgn : g ∣ n)
    (hp : 0 < (k : ℝ)/m + (l : ℝ)/n - 1) :
    (g : ℝ)/((m : ℝ)*n) ≤ (k : ℝ)/m + (l : ℝ)/n - 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 := hmR.ne'
  have hn0 := hnR.ne'
  have he : ((k : ℝ)/m + (l : ℝ)/n - 1)*((m : ℝ)*n) =
      ((n*k+m*l : ℕ) : ℝ) - ((m*n : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hpositive := mul_pos hp (mul_pos hmR hnR)
  rw [he] at hpositive
  have hN : m*n < n*k+m*l := by exact_mod_cast (sub_pos.mp hpositive)
  have hd : g ∣ n*k+m*l-m*n := Nat.dvd_sub
    (dvd_add (dvd_mul_of_dvd_left hgn k) (dvd_mul_of_dvd_left hgm l))
    (dvd_mul_of_dvd_left hgm n)
  have hnum : (g : ℝ) ≤ ((n*k+m*l-m*n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.sub_pos_of_lt hN) hd
  rw [Nat.cast_sub hN.le] at hnum
  apply (div_le_iff₀ (mul_pos hmR hnR)).mpr
  rw [he]
  exact hnum

/-- The original Pang-method grid bound is the common-divisor-one case. -/
theorem positive_rectangular_cut_grid_one {m n k l : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < (k : ℝ)/m + (l : ℝ)/n - 1) :
    1/((m : ℝ)*n) ≤ (k : ℝ)/m + (l : ℝ)/n - 1 := by
  simpa only [Nat.cast_one] using
    positive_rectangular_cut_grid hm hn (one_dvd m) (one_dvd n) hp

/-- The arithmetic refinement retains the full gcd gain. -/
theorem positive_rectangular_cut_grid_gcd {m n k l : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < (k : ℝ)/m + (l : ℝ)/n - 1) :
    (Nat.gcd m n : ℝ)/((m : ℝ)*n) ≤ (k : ℝ)/m + (l : ℝ)/n - 1 :=
  positive_rectangular_cut_grid hm hn (Nat.gcd_dvd_left m n) (Nat.gcd_dvd_right m n) hp

end DittertRybin
