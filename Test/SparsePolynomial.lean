import DR.Certificates.SparsePolynomialTensor

namespace DittertRybin.Tests.SparsePolynomial
open DittertRybin.Certificates.SparsePolynomial

-- Exact cancellation removes the coefficient; zero factors produce no terms.
example : sub (var 0) (var 0) = [] := by decide +kernel
example : mul (constant 0) (var 1) = [] := by decide +kernel
example : mul (var 2) (constant 0) = [] := by decide +kernel

-- Independent exponent coordinates, signed coefficients, and normalization order.
example : mul (add (var 0) (var 1)) (sub (var 0) (var 1)) =
    [((2,0,0),1), ((0,2,0),-1)] := by decide +kernel
example : ¬ mul (add (var 0) (var 1)) (sub (var 0) (var 1)) =
    [((2,0,0),1), ((0,2,0),1)] := by decide +kernel
example : mul (pow (var 0) 63) (var 0) = [((64,0,0),1)] := by decide +kernel

-- Rational multiplication preserves its denominator and sign.
example : mul (constant (2/3)) (constant (-9/2)) = constant (-3) := by decide +kernel
example : pow (constant 0) 0 = constant 1 := by decide +kernel

-- Empty finite tensor dimensions represent exactly zero.
example : fromTensor (fun i : Fin 0 => fun _ : Fin 2 => fun _ : Fin 2 =>
    (Fin.elim0 i : ℚ)) = [] := by decide +kernel

-- A dense tensor includes zero entries; they must not survive as sparse terms.
example : fromTensor (fun i j k : Fin 2 =>
    if i = 0 ∧ j = 1 ∧ k = 0 then (2 : ℚ) else 0) =
      [((0,0,1),2)] := by decide +kernel
example : add [((7,2,3),0)] [((0,1,0),0)] = [] := by decide +kernel

#print axioms DittertRybin.Certificates.SparsePolynomial.value_mul
#print axioms DittertRybin.Certificates.SparsePolynomial.value_pow
#print axioms DittertRybin.Certificates.SparsePolynomial.value_fromTensor
#print axioms DittertRybin.Certificates.SparsePolynomial.value_mergeAux
end DittertRybin.Tests.SparsePolynomial
