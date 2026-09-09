import DR.Certificates.FiniteK3EnvelopeEntries
import DR.Certificates.FiniteK3Ordinary

/-! Actual rational small blocks and their proven compact evaluation formulas.
The ordering is row-major distinguished cells followed by aggregate rows. -/
namespace DittertRybin.Certificates
open scoped BigOperators

def finiteK3EnvelopeColumn {k : Nat} (hk : k≤2) : Fin k ⊕ Bool → Fin 4
  | .inl j => j.castLE (by omega)
  | .inr b => ⟨k+(if b then 1 else 0),by cases b <;> simp <;> omega⟩

theorem finiteK3EnvelopeColumn_injective {k : Nat} (hk : k≤2) :
    Function.Injective (finiteK3EnvelopeColumn hk) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  rcases a with a | a <;> rcases b with b | b
  · apply congrArg Sum.inl
    exact Fin.ext hv
  · cases b <;> simp [finiteK3EnvelopeColumn] at hv <;> omega
  · cases a <;> simp [finiteK3EnvelopeColumn] at hv <;> omega
  · cases a <;> cases b <;> simp_all [finiteK3EnvelopeColumn]

theorem finiteK3DistinguishedColumns_le_two (s : Fin 4) : finiteK3DistinguishedColumns s≤2 := by
  unfold finiteK3DistinguishedColumns
  omega

theorem finiteK3EnvelopeEntry_included {R : Type*} (coeff : Fin 93 → R)
    (m : Nat) (hm : 2≤m) (hm9 : m≤9) (s : Fin 4)
    (a b : Fin m × (Fin (finiteK3DistinguishedColumns s) ⊕ Bool)) :
    finiteK3Entry coeff ((finiteK3FirstCell m hm s).1,Sum.inl (finiteK3FirstCell m hm s).2)
      ((finiteK3SecondCell m hm s).1,Sum.inl (finiteK3SecondCell m hm s).2) a b =
      finiteK3EnvelopeEntry coeff s
        (a.1.castLE hm9,finiteK3EnvelopeColumn (finiteK3DistinguishedColumns_le_two s) a.2)
        (b.1.castLE hm9,finiteK3EnvelopeColumn (finiteK3DistinguishedColumns_le_two s) b.2) := by
  rw [finiteK3EnvelopeEntry_eq]
  exact (finiteK3Entry_map coeff (Fin.castLE hm9)
    (finiteK3EnvelopeColumn (finiteK3DistinguishedColumns_le_two s))
    (Fin.castLE_injective hm9) (finiteK3EnvelopeColumn_injective _)
    ((finiteK3FirstCell m hm s).1,Sum.inl (finiteK3FirstCell m hm s).2)
    ((finiteK3SecondCell m hm s).1,Sum.inl (finiteK3SecondCell m hm s).2) a b).symm

/-- Fast evaluation of the same actual entry on distinguished/virtual ordinary cells. -/
def finiteK3EnvelopeVirtual {R : Type*} (coeff : Fin 93 → R) (m : Nat) (hm9 : m≤9)
    (s : Fin 4) (a b : Fin m × (Fin (finiteK3DistinguishedColumns s) ⊕ Bool)) : R :=
  finiteK3EnvelopeEntry coeff s
    (a.1.castLE hm9,finiteK3EnvelopeColumn (finiteK3DistinguishedColumns_le_two s) a.2)
    (b.1.castLE hm9,finiteK3EnvelopeColumn (finiteK3DistinguishedColumns_le_two s) b.2)

def finiteK3EnvelopeTableH (coeff : Fin 93 → ℚ) (m : Nat) (hm9 : m≤9) (s : Fin 4) :
    Matrix (Fin m) (Fin m) ℚ := fun i j =>
  finiteK3EnvelopeVirtual coeff m hm9 s (i,Sum.inr false) (j,Sum.inr false)-
    finiteK3EnvelopeVirtual coeff m hm9 s (i,Sum.inr false) (j,Sum.inr true)

def finiteK3EnvelopeH (coeff : Fin 93 → ℚ) (m : Nat) (hm : 2≤m) (s : Fin 4) :
    Matrix (Fin m) (Fin m) ℚ :=
  finiteK3OrdinaryH coeff (finiteK3FirstCell m hm s) (finiteK3SecondCell m hm s)

theorem finiteK3EnvelopeH_eq_table (coeff : Fin 93 → ℚ) (m : Nat)
    (hm : 2≤m) (hm9 : m≤9) (s : Fin 4) :
    finiteK3EnvelopeH coeff m hm s=finiteK3EnvelopeTableH coeff m hm9 s := by
  ext i j
  simp only [finiteK3EnvelopeH,finiteK3OrdinaryH,Matrix.sub_apply,
    finiteK3OrdinaryD,finiteK3OrdinaryO,finiteK3EnvelopeTableH,
    finiteK3EnvelopeVirtual,finiteK3EnvelopeEntry_included coeff m hm hm9 s]

def finiteK3EnvelopeTableB (coeff : Fin 93 → ℚ) (m n : Nat) (hm9 : m≤9) (s : Fin 4) :
    Matrix ((Fin m × Fin (finiteK3DistinguishedColumns s)) ⊕ Fin m)
      ((Fin m × Fin (finiteK3DistinguishedColumns s)) ⊕ Fin m) ℚ
  | .inl a,.inl b => finiteK3EnvelopeVirtual coeff m hm9 s (a.1,Sum.inl a.2) (b.1,Sum.inl b.2)
  | .inl a,.inr b => finiteK3EnvelopeVirtual coeff m hm9 s (a.1,Sum.inl a.2) (b,Sum.inr false)
  | .inr a,.inl b => finiteK3EnvelopeVirtual coeff m hm9 s (b.1,Sum.inl b.2) (a,Sum.inr false)
  | .inr a,.inr b =>
    finiteK3EnvelopeVirtual coeff m hm9 s (a,Sum.inr false) (b,Sum.inr true)+
      (finiteK3EnvelopeVirtual coeff m hm9 s (a,Sum.inr false) (b,Sum.inr false)-
        finiteK3EnvelopeVirtual coeff m hm9 s (a,Sum.inr false) (b,Sum.inr true))/
          (n-finiteK3DistinguishedColumns s:Nat)

def finiteK3EnvelopeB (coeff : Fin 93 → ℚ) (m n : Nat) (hm : 2≤m) (s : Fin 4) :=
  finiteK3OrdinaryB coeff (finiteK3FirstCell m hm s) (finiteK3SecondCell m hm s)
    (n-finiteK3DistinguishedColumns s:Nat)

theorem finiteK3EnvelopeB_eq_table (coeff : Fin 93 → ℚ) (m n : Nat)
    (hm : 2≤m) (hm9 : m≤9) (s : Fin 4) :
    finiteK3EnvelopeB coeff m n hm s=finiteK3EnvelopeTableB coeff m n hm9 s := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · have hmap := finiteK3Entry_map coeff id
      (@Sum.inl (Fin (finiteK3DistinguishedColumns s)) Bool)
      Function.injective_id Sum.inl_injective
      (finiteK3FirstCell m hm s) (finiteK3SecondCell m hm s) a b
    exact hmap.symm.trans (finiteK3EnvelopeEntry_included coeff m hm hm9 s _ _)
  · exact finiteK3EnvelopeEntry_included coeff m hm hm9 s _ _
  · exact finiteK3EnvelopeEntry_included coeff m hm hm9 s _ _
  · simp only [finiteK3EnvelopeB,finiteK3OrdinaryB,finiteK3OrdinaryD,finiteK3OrdinaryO,
      finiteK3EnvelopeTableB,finiteK3EnvelopeVirtual,finiteK3EnvelopeEntry_included coeff m hm hm9 s]

def finiteK3EnvelopeFlatB (coeff : Fin 93 → ℚ) (m n : Nat) (hm : 2≤m) (s : Fin 4) :=
  (finiteK3EnvelopeB coeff m n hm s).submatrix
    (finiteK3AggregateEquiv m (finiteK3DistinguishedColumns s)).symm
    (finiteK3AggregateEquiv m (finiteK3DistinguishedColumns s)).symm

def finiteK3EnvelopeFlatTableB (coeff : Fin 93 → ℚ) (m n : Nat) (hm9 : m≤9) (s : Fin 4) :=
  (finiteK3EnvelopeTableB coeff m n hm9 s).submatrix
    (finiteK3AggregateEquiv m (finiteK3DistinguishedColumns s)).symm
    (finiteK3AggregateEquiv m (finiteK3DistinguishedColumns s)).symm

theorem finiteK3EnvelopeFlatB_eq_table (coeff : Fin 93 → ℚ) (m n : Nat)
    (hm : 2≤m) (hm9 : m≤9) (s : Fin 4) :
    finiteK3EnvelopeFlatB coeff m n hm s=finiteK3EnvelopeFlatTableB coeff m n hm9 s := by
  rw [finiteK3EnvelopeFlatB,finiteK3EnvelopeB_eq_table]
  rfl

def finiteK3EnvelopeKernel (m n : Nat) (s : Fin 4)
    (i : Fin (m*finiteK3DistinguishedColumns s+m)) : ℚ :=
  if i.val<m*finiteK3DistinguishedColumns s then 1 else (n-finiteK3DistinguishedColumns s:Nat)

end DittertRybin.Certificates
