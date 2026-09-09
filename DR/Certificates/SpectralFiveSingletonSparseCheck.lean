import DR.Certificates.SpectralFiveSingletonSparseStages
import DR.Certificates.SpectralFiveSingletonSparseTensorCheck

/-! The complete exact numerator identity, assembled from bounded rational arithmetic checks. -/
namespace DittertRybin.Certificates.SpectralFiveSingleton

/-- Every coefficient is derived from the literal factored source; no polynomial identity is assumed. -/
theorem singletonSparseCheck : SparseSource.scaledSingletonPolynomial =
    SparsePolynomial.fromTensor singletonPowerCoefficients :=
  SparseStages.scaledSingletonPolynomial_checked.trans SparseStages.final_tensor_checked

end DittertRybin.Certificates.SpectralFiveSingleton
