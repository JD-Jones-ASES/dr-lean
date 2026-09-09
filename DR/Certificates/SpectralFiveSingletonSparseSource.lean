import DR.Certificates.SparsePolynomialTensor
import DR.Certificates.SpectralFiveSingletonPolynomial

/-! The literal factored singleton numerator interpreted by exact sparse arithmetic. -/
namespace DittertRybin.Certificates.SpectralFiveSingleton
namespace SparseSource

def uPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant (23 / 50)) (SparsePolynomial.var 0)) (SparsePolynomial.var 1))

def vPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant (1 / 2)) (SparsePolynomial.var 0)) (SparsePolynomial.var 2))

def lowerPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.constant 1) (SparsePolynomial.mul (SparsePolynomial.constant (23 / 50)) (SparsePolynomial.var 0)))

def qPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.constant 1) (SparsePolynomial.var 0))

def heightPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.add (SparsePolynomial.constant 1) (SparsePolynomial.mul (SparsePolynomial.constant (1 / 2)) (SparsePolynomial.var 0)))

def energyPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.mul heightPolynomial (SparsePolynomial.sub (SparsePolynomial.constant (24 / 625)) (SparsePolynomial.mul (SparsePolynomial.constant ((1 - 24 / 625) / 5)) (SparsePolynomial.pow (SparsePolynomial.var 0) 2))))

def denominatorPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.constant (19 / 100)) qPolynomial) energyPolynomial)

def crossingPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.mul energyPolynomial (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.constant 2) qPolynomial) energyPolynomial))

def anPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant 2) denominatorPolynomial) (SparsePolynomial.sub (SparsePolynomial.add (SparsePolynomial.constant 2) vPolynomial) uPolynomial)) crossingPolynomial)

def snPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant 2) denominatorPolynomial) (SparsePolynomial.sub (SparsePolynomial.add (SparsePolynomial.constant 8) uPolynomial) vPolynomial)) crossingPolynomial)

def rnPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant 2) denominatorPolynomial) (SparsePolynomial.sub (SparsePolynomial.sub (SparsePolynomial.constant 2) (SparsePolynomial.mul (SparsePolynomial.constant 3) uPolynomial)) vPolynomial)) crossingPolynomial)

def cnPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant 2) denominatorPolynomial) (SparsePolynomial.add (SparsePolynomial.add (SparsePolynomial.mul (SparsePolynomial.constant 2) lowerPolynomial) uPolynomial) vPolynomial)) crossingPolynomial)

def commonPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.pow (SparsePolynomial.sub (SparsePolynomial.constant 1) uPolynomial) 2) lowerPolynomial) (SparsePolynomial.add (SparsePolynomial.constant 1) vPolynomial))

def enPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.add (SparsePolynomial.constant 5) (SparsePolynomial.pow (SparsePolynomial.var 0) 2)) (SparsePolynomial.constant 16384)) (SparsePolynomial.pow denominatorPolynomial 3)) (SparsePolynomial.add (SparsePolynomial.mul (SparsePolynomial.mul rnPolynomial lowerPolynomial) (SparsePolynomial.add (SparsePolynomial.constant 1) vPolynomial)) (SparsePolynomial.mul cnPolynomial (SparsePolynomial.pow (SparsePolynomial.sub (SparsePolynomial.constant 1) uPolynomial) 2)))) (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.pow (SparsePolynomial.var 0) 2) (SparsePolynomial.pow (SparsePolynomial.mul (SparsePolynomial.constant 16) denominatorPolynomial) 4)) commonPolynomial)) (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant (61 / 32)) (SparsePolynomial.pow snPolynomial 4)) commonPolynomial) (SparsePolynomial.add (SparsePolynomial.constant 5) (SparsePolynomial.pow (SparsePolynomial.var 0) 2))))

def singletonPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.sub (SparsePolynomial.mul anPolynomial enPolynomial) (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.constant 4) denominatorPolynomial) (SparsePolynomial.sub (SparsePolynomial.mul (SparsePolynomial.constant (24 / 625)) (SparsePolynomial.add (SparsePolynomial.constant 5) (SparsePolynomial.pow (SparsePolynomial.var 0) 2))) (SparsePolynomial.pow (SparsePolynomial.var 0) 2))) (SparsePolynomial.pow (SparsePolynomial.mul (SparsePolynomial.constant 16) denominatorPolynomial) 4)) commonPolynomial))

def singletonScale : ℚ := 727595761418342590332031250000000000000000000

def scaledSingletonPolynomial : SparsePolynomial.Polynomial :=
  (SparsePolynomial.mul (SparsePolynomial.constant (singletonScale)) singletonPolynomial)

end SparseSource

theorem singletonSparseSource_value :
    SparsePolynomial.value (fun i : Fin 3 => (MvPolynomial.X i : MvPolynomial (Fin 3) ℚ))
      SparseSource.scaledSingletonPolynomial = scaledSingletonPolynomial := by
  simp only [SparseSource.scaledSingletonPolynomial, SparseSource.singletonScale, SparseSource.singletonPolynomial, SparseSource.enPolynomial, SparseSource.anPolynomial, SparseSource.snPolynomial, SparseSource.rnPolynomial, SparseSource.cnPolynomial, SparseSource.commonPolynomial, SparseSource.crossingPolynomial, SparseSource.denominatorPolynomial, SparseSource.energyPolynomial, SparseSource.heightPolynomial, SparseSource.qPolynomial, SparseSource.lowerPolynomial, SparseSource.uPolynomial, SparseSource.vPolynomial,
    SparsePolynomial.value_add, SparsePolynomial.value_mul, SparsePolynomial.value_sub,
    SparsePolynomial.value_pow, SparsePolynomial.value_constant, SparsePolynomial.value_variable,
    MvPolynomial.algebraMap_eq, map_ofNat, map_one]
  simp only [scaledSingletonPolynomial, singletonScale, singletonPolynomial, enPolynomial, anPolynomial, snPolynomial, rnPolynomial, cnPolynomial, commonPolynomial, crossingPolynomial, denominatorPolynomial, energyPolynomial, heightPolynomial, qPolynomial, lowerPolynomial, uPolynomial, vPolynomial, map_ofNat]

end DittertRybin.Certificates.SpectralFiveSingleton
