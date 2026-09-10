import DR.Certificates.BernsteinTransform
import Mathlib.Tactic.FinCases

/-! Exact repeated-row minorant coefficients after rational compactification.
Regenerate with `scripts/generate_four_row_minorant.py --check`.
The common coefficient denominator is 1122^3 = 1412467848. -/

namespace DittertRybin.Certificates.FourRowMinorant

/-- Literal coefficients in the compactified (X,T,Z) polynomial. -/
def compactPowerCoefficient (a b c : Fin 3) : ℤ :=
  match a.val, b.val, c.val with
  | 2, 2, 2 => 16
  | 2, 2, 1 => -16
  | 2, 1, 2 => -32
  | 2, 1, 1 => 48
  | 2, 1, 0 => -16
  | 2, 0, 2 => 16
  | 2, 0, 1 => -32
  | 2, 0, 0 => 16
  | 1, 2, 2 => -12
  | 1, 2, 1 => 8
  | 1, 1, 1 => 8
  | 1, 1, 0 => -4
  | 1, 0, 2 => 12
  | 1, 0, 1 => -16
  | 1, 0, 0 => 4
  | 0, 2, 2 => -4
  | 0, 2, 1 => 8
  | 0, 1, 2 => 6
  | 0, 1, 1 => -11
  | 0, 1, 0 => 2
  | 0, 0, 1 => 1
  | _, _, _ => 0

/-- Numerators for choose(i,k)/choose(34,k), k=0,1,2, over denominator1122. -/
def degree34MomentNumerator (a : Fin 3) (i : Fin 35) : ℤ :=
  match a.val with
  | 0 => 1122
  | 1 => 33*(i.val:ℤ)
  | _ => (i.val:ℤ)*((i.val:ℤ)-1)

/-- The exact numerator of each of the 42,875 elevated Bernstein coefficients. -/
def compactBernsteinNumerator (i j k : Fin 35) : ℤ :=
    (16)*degree34MomentNumerator 2 i*degree34MomentNumerator 2 j*degree34MomentNumerator 2 k +
    (-16)*degree34MomentNumerator 2 i*degree34MomentNumerator 2 j*degree34MomentNumerator 1 k +
    (-32)*degree34MomentNumerator 2 i*degree34MomentNumerator 1 j*degree34MomentNumerator 2 k +
    (48)*degree34MomentNumerator 2 i*degree34MomentNumerator 1 j*degree34MomentNumerator 1 k +
    (-16)*degree34MomentNumerator 2 i*degree34MomentNumerator 1 j*degree34MomentNumerator 0 k +
    (16)*degree34MomentNumerator 2 i*degree34MomentNumerator 0 j*degree34MomentNumerator 2 k +
    (-32)*degree34MomentNumerator 2 i*degree34MomentNumerator 0 j*degree34MomentNumerator 1 k +
    (16)*degree34MomentNumerator 2 i*degree34MomentNumerator 0 j*degree34MomentNumerator 0 k +
    (-12)*degree34MomentNumerator 1 i*degree34MomentNumerator 2 j*degree34MomentNumerator 2 k +
    (8)*degree34MomentNumerator 1 i*degree34MomentNumerator 2 j*degree34MomentNumerator 1 k +
    (8)*degree34MomentNumerator 1 i*degree34MomentNumerator 1 j*degree34MomentNumerator 1 k +
    (-4)*degree34MomentNumerator 1 i*degree34MomentNumerator 1 j*degree34MomentNumerator 0 k +
    (12)*degree34MomentNumerator 1 i*degree34MomentNumerator 0 j*degree34MomentNumerator 2 k +
    (-16)*degree34MomentNumerator 1 i*degree34MomentNumerator 0 j*degree34MomentNumerator 1 k +
    (4)*degree34MomentNumerator 1 i*degree34MomentNumerator 0 j*degree34MomentNumerator 0 k +
    (-4)*degree34MomentNumerator 0 i*degree34MomentNumerator 2 j*degree34MomentNumerator 2 k +
    (8)*degree34MomentNumerator 0 i*degree34MomentNumerator 2 j*degree34MomentNumerator 1 k +
    (6)*degree34MomentNumerator 0 i*degree34MomentNumerator 1 j*degree34MomentNumerator 2 k +
    (-11)*degree34MomentNumerator 0 i*degree34MomentNumerator 1 j*degree34MomentNumerator 1 k +
    (2)*degree34MomentNumerator 0 i*degree34MomentNumerator 1 j*degree34MomentNumerator 0 k +
    (1)*degree34MomentNumerator 0 i*degree34MomentNumerator 0 j*degree34MomentNumerator 1 k

end DittertRybin.Certificates.FourRowMinorant
