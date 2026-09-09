import DR.Certificates.SpectralFiveSingletonData
import DR.Certificates.SpectralFiveSingletonPowerData
import DR.Certificates.BernsteinTransform
import Mathlib.Tactic.FinCases

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators
open MvPolynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def singletonCoefficientMatch (i : Fin 8) (j : Fin 7) : Prop :=
  ∀ k : Fin 37, blockPowerCoefficients i j k =
    powerToBernstein (fun b : Fin 7 => powerToBernstein
      (fun a : Fin 8 => singletonPowerCoefficients a b k) i) j

end
end DittertRybin.Certificates.SpectralFiveSingleton
