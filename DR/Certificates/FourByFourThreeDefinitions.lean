import DR.Certificates.FourByFourThreeData
import Mathlib.Logic.Equiv.Fin.Basic

/-! The 17 specified pair entries of the cubic 4x4 certificate. Every multiplier
matrix is an actual row/column-swap conjugate of this anchor seed. -/
namespace DittertRybin.Certificates
open scoped BigOperators

def fourByFourThreeCell : (Fin 4 × Fin 4) ≃ Fin 16 := finProdFinEquiv

def fourByFourThreeClass (a : Fin 16) : ℕ :=
  if a.val/4=0 then (if a.val%4=0 then 0 else 1) else (if a.val%4=0 then 2 else 3)

/-- Numerators in the documented factor-64 convention. -/
def fourByFourThreeSeedCode (a b : Fin 16) : ℤ :=
  match fourByFourThreeClass a,fourByFourThreeClass b with
  | 0,0 => 39
  | 0,1 | 1,0 | 0,2 | 2,0 => -2
  | 0,3 | 3,0 => -3
  | 1,1 => if a.val%4=b.val%4 then 121 else -25
  | 2,2 => if a.val/4=b.val/4 then 121 else -25
  | 1,2 | 2,1 => 21
  | 1,3 | 3,1 => if a.val%4=b.val%4 then 48 else -46
  | 2,3 | 3,2 => if a.val/4=b.val/4 then 48 else -46
  | _,_ => if a=b then 123 else if a.val/4=b.val/4 ∨ a.val%4=b.val%4 then 17 else -25

def fourByFourThreeSeed : Matrix (Fin 16) (Fin 16) ℚ :=
  fun a b => (fourByFourThreeSeedCode a b:ℚ)/64

def fourByFourThreeShift : Matrix (Fin 16) (Fin 16) ℚ :=
  fourByFourThreeSeed-(1/20:ℚ) • centeringMatrix 16

/-- The literal swaps taking the anchor cell (0,0) to multiplier e. -/
def fourByFourThreeSwap (e : Fin 16) : Equiv.Perm (Fin 16) :=
  fourByFourThreeCell.symm.trans
    ((Equiv.prodCongr (Equiv.swap 0 (fourByFourThreeCell.symm e).1)
      (Equiv.swap 0 (fourByFourThreeCell.symm e).2)).trans fourByFourThreeCell)

def fourByFourThreeMatrix (e : Fin 16) : Matrix (Fin 16) (Fin 16) ℚ :=
  fourByFourThreeSeed.submatrix (fourByFourThreeSwap e) (fourByFourThreeSwap e)

end DittertRybin.Certificates
