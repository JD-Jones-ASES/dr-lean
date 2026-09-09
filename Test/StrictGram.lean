import DR.Certificates.StrictGram

namespace DittertRybin.Certificates.Tests

def unitGram : GramCertificate 1 1 := ⟨fun _ => 1,fun _ _ => 1⟩
def zeroPivotGram : GramCertificate 1 1 := ⟨fun _ => 0,fun _ _ => 1⟩
def zeroFactorGram : GramCertificate 1 1 := ⟨fun _ => 1,fun _ _ => 0⟩

example : unitGram.StrictValid (Matrix.of (fun _ _ : Fin 1 => (1:ℚ))) := by decide +kernel
example : zeroPivotGram.Valid (Matrix.of (fun _ _ : Fin 1 => (0:ℚ))) ∧
    ¬zeroPivotGram.StrictValid (Matrix.of (fun _ _ : Fin 1 => (0:ℚ))) := by decide +kernel
example : zeroFactorGram.Valid (Matrix.of (fun _ _ : Fin 1 => (0:ℚ))) ∧
    ¬zeroFactorGram.StrictValid (Matrix.of (fun _ _ : Fin 1 => (0:ℚ))) := by decide +kernel
example : ¬unitGram.StrictValid (Matrix.of (fun _ _ : Fin 1 => (2:ℚ))) := by decide +kernel
example {n : Nat} (C : GramCertificate n n) (Q : Matrix (Fin n) (Fin n) ℚ)
    (hC : C.StrictValid Q) : (Q.map (fun q : ℚ => (q:ℝ))).PosDef :=
  C.strictValid_posDef Q hC

#print axioms GramCertificate.strictValid_posDef
end DittertRybin.Certificates.Tests
