import DR.Certificates.Gram

/-! A compact exact strict LDL gate, using the existing Gram representation.
The factor is upper triangular (L-transpose) with a positive diagonal. -/
namespace DittertRybin.Certificates
namespace GramCertificate
open scoped BigOperators

def StrictValid {n : Nat} (C : GramCertificate n n) (Q : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  C.Valid Q ∧ (∀ a,0<C.weights a) ∧
    (∀ i j,i<j → C.factor j i=0) ∧ ∀ i,0<C.factor i i

instance {n : Nat} (C : GramCertificate n n) (Q : Matrix (Fin n) (Fin n) ℚ) :
    Decidable (C.StrictValid Q) := by
  unfold StrictValid
  infer_instance

theorem strictValid_posDef {n : Nat} (C : GramCertificate n n)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hC : C.StrictValid Q) :
    (Q.map (fun q : ℚ => (q:ℝ))).PosDef := by
  let L : Matrix (Fin n) (Fin n) ℚ := fun i j => C.factor j i
  apply ofLDL_posDef L C.weights Q hC.2.1
  · intro i j
    rw [hC.1.2 i j]
    unfold weightedGram
    apply Finset.sum_congr rfl
    intro a _
    dsimp [L]
    ring
  · exact hC.2.2.1
  · intro i
    exact ne_of_gt (hC.2.2.2 i)

end GramCertificate
end DittertRybin.Certificates
