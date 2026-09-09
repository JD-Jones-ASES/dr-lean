import DR.Certificates.BernsteinTransform

/-! The literal singleton numerator from order-five Appendix B, before its exact tensor decomposition. -/
namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open MvPolynomial
open scoped BigOperators

def uPolynomial : MvPolynomial (Fin 3) ℚ := C (23/50) * X 0 * X 1
def vPolynomial : MvPolynomial (Fin 3) ℚ := C (1/2) * X 0 * X 2
def lowerPolynomial : MvPolynomial (Fin 3) ℚ := 1 - C (23/50) * X 0
def qPolynomial : MvPolynomial (Fin 3) ℚ := 1 - X 0
def heightPolynomial : MvPolynomial (Fin 3) ℚ := 1 + C (1/2) * X 0
def energyPolynomial : MvPolynomial (Fin 3) ℚ :=
  heightPolynomial * (C (24/625) - C ((1-24/625)/5) * X 0 ^ 2)
def denominatorPolynomial : MvPolynomial (Fin 3) ℚ := C (19/100) * qPolynomial - energyPolynomial
def crossingPolynomial : MvPolynomial (Fin 3) ℚ := energyPolynomial * (2 * qPolynomial - energyPolynomial)
def anPolynomial : MvPolynomial (Fin 3) ℚ := 2 * denominatorPolynomial * (2 + vPolynomial - uPolynomial) - crossingPolynomial
def snPolynomial : MvPolynomial (Fin 3) ℚ := 2 * denominatorPolynomial * (8 + uPolynomial - vPolynomial) - crossingPolynomial
def rnPolynomial : MvPolynomial (Fin 3) ℚ := 2 * denominatorPolynomial * (2 - 3 * uPolynomial - vPolynomial) - crossingPolynomial
def cnPolynomial : MvPolynomial (Fin 3) ℚ := 2 * denominatorPolynomial * (2 * lowerPolynomial + uPolynomial + vPolynomial) - crossingPolynomial
def commonPolynomial : MvPolynomial (Fin 3) ℚ := (1-uPolynomial)^2 * lowerPolynomial * (1+vPolynomial)
def enPolynomial : MvPolynomial (Fin 3) ℚ :=
  (5+X 0^2)*16384*denominatorPolynomial^3 *
    (rnPolynomial*lowerPolynomial*(1+vPolynomial) + cnPolynomial*(1-uPolynomial)^2) -
  X 0^2*(16*denominatorPolynomial)^4*commonPolynomial -
  C (61/32)*snPolynomial^4*commonPolynomial*(5+X 0^2)
def singletonPolynomial : MvPolynomial (Fin 3) ℚ :=
  anPolynomial*enPolynomial - 4*denominatorPolynomial*(C (24/625)*(5+X 0^2)-X 0^2)*
    (16*denominatorPolynomial)^4*commonPolynomial

def singletonScale : ℚ := 727595761418342590332031250000000000000000000

def scaledSingletonPolynomial : MvPolynomial (Fin 3) ℚ := C singletonScale * singletonPolynomial

theorem singletonScale_pos : 0 < singletonScale := by norm_num [singletonScale]
end
end DittertRybin.Certificates.SpectralFiveSingleton
