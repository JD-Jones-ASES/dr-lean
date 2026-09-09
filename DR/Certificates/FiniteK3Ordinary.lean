import DR.Certificates.FiniteK3Orbits
import DR.Certificates.OrdinaryColumnBlocks
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual equality-pattern seed matrices on distinguished and ordinary columns.
The virtual ordinary labels used in the small blocks are justified by equality
relations of physical cells, independently of the number of ordinary columns. -/
namespace DittertRybin.Certificates

variable {ρ δ γ : Type*} [DecidableEq ρ] [DecidableEq δ] [DecidableEq γ]

/-- Row-major distinguished cells, followed by the aggregate ordinary rows. -/
def finiteK3AggregateEquiv (m k : ℕ) :
    ((Fin m × Fin k) ⊕ Fin m) ≃ Fin (m * k + m) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin m))).trans finSumFinEquiv

/-- The aggregate kernel corresponding to a constant full-cell vector. -/
def finiteK3AggregateKernel {R : Type*} [One R] (ell : R) : ((ρ × δ) ⊕ ρ) → R :=
  Sum.elim (fun _ => 1) (fun _ => ell)

theorem finiteK3AggregateEquiv_left {m k : ℕ} (i : Fin m) (j : Fin k) :
    finiteK3AggregateEquiv m k (.inl (i,j)) = Fin.castAdd m (finProdFinEquiv (i,j)) := rfl

theorem finiteK3AggregateEquiv_right {m k : ℕ} (i : Fin m) :
    finiteK3AggregateEquiv m k (.inr i) = Fin.natAdd (m*k) i := rfl

/-- Reindex cells by whether their column is distinguished or ordinary. -/
def ordinaryCellEquiv : ((ρ × δ) ⊕ (γ × ρ)) ≃ (ρ × (δ ⊕ γ)) where
  toFun := Sum.elim (fun p => (p.1,Sum.inl p.2)) (fun p => (p.2,Sum.inr p.1))
  invFun := fun p => match p.2 with
    | .inl d => .inl (p.1,d)
    | .inr c => .inr (c,p.1)
  left_inv := by intro p; rcases p with p | p <;> rfl
  right_inv := by intro p; rcases p with ⟨r,c⟩; rcases c <;> rfl

def finiteK3OrdinaryA {R : Type*} (coeff : Fin 93 → R) (e f : ρ × δ) :
    Matrix (ρ × δ) (ρ × δ) R := finiteK3Entry coeff e f

def finiteK3OrdinaryG {R : Type*} (coeff : Fin 93 → R) (e f : ρ × δ) :
    Matrix (ρ × δ) ρ R := fun a b =>
  finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
    (a.1,Sum.inl a.2) ((b,Sum.inr false) : ρ × (δ ⊕ Bool))

def finiteK3OrdinaryD {R : Type*} (coeff : Fin 93 → R) (e f : ρ × δ) :
    Matrix ρ ρ R := fun a b =>
  finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
    (a,Sum.inr false) ((b,Sum.inr false) : ρ × (δ ⊕ Bool))

def finiteK3OrdinaryO {R : Type*} (coeff : Fin 93 → R) (e f : ρ × δ) :
    Matrix ρ ρ R := fun a b =>
  finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
    (a,Sum.inr false) ((b,Sum.inr true) : ρ × (δ ⊕ Bool))

theorem finiteK3Ordinary_left_left (coeff : Fin 93 → ℝ) (e f a b : ρ × δ) :
    finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
      (a.1,Sum.inl a.2) ((b.1,Sum.inl b.2) : ρ × (δ ⊕ γ)) =
        finiteK3OrdinaryA coeff e f a b := by
  exact finiteK3Entry_map coeff id Sum.inl Function.injective_id Sum.inl_injective e f a b

theorem finiteK3Ordinary_left_right (coeff : Fin 93 → ℝ) (e f a : ρ × δ)
    (b : ρ) (c : γ) :
    finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
      (a.1,Sum.inl a.2) ((b,Sum.inr c) : ρ × (δ ⊕ γ)) =
        finiteK3OrdinaryG coeff e f a b := by
  apply congrArg coeff
  apply finiteK3Role_congr
  · intro i j; rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> simp

theorem finiteK3Ordinary_right_right (coeff : Fin 93 → ℝ) (e f : ρ × δ)
    (a b : ρ) (c d : γ) :
    finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
      (a,Sum.inr c) ((b,Sum.inr d) : ρ × (δ ⊕ γ)) =
        if c=d then finiteK3OrdinaryD coeff e f a b else finiteK3OrdinaryO coeff e f a b := by
  by_cases hcd : c=d
  · subst d
    rw [if_pos rfl]
    apply congrArg coeff
    apply finiteK3Role_congr
    · intro i j; rfl
    · intro i j
      fin_cases i <;> fin_cases j <;> simp
  · rw [if_neg hcd]
    apply congrArg coeff
    apply finiteK3Role_congr
    · intro i j; rfl
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [hcd,Ne.symm hcd]

/-- The full physical seed is exactly the ordinary-column matrix. -/
theorem finiteK3Entry_ordinaryColumnMatrix (coeff : Fin 93 → ℝ) (e f : ρ × δ) :
    Matrix.submatrix (finiteK3Entry coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2) :
      Matrix (ρ × (δ ⊕ γ)) (ρ × (δ ⊕ γ)) ℝ) ordinaryCellEquiv ordinaryCellEquiv =
        ordinaryColumnMatrix (γ := γ) (finiteK3OrdinaryA coeff e f)
          (finiteK3OrdinaryG coeff e f) (finiteK3OrdinaryD coeff e f) (finiteK3OrdinaryO coeff e f) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q
  · exact finiteK3Ordinary_left_left coeff e f p q
  · exact finiteK3Ordinary_left_right coeff e f p q.2 q.1
  · change finiteK3Entry coeff _ _ _ _ = _
    rw [finiteK3Entry_symmetric]
    exact finiteK3Ordinary_left_right coeff e f q p.2 p.1
  · exact finiteK3Ordinary_right_right coeff e f p.2 q.2 p.1 q.1

theorem finiteK3OrdinaryA_isSymm (coeff : Fin 93 → ℝ) (e f : ρ × δ) :
    (finiteK3OrdinaryA coeff e f).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  exact finiteK3Entry_symmetric coeff e f a b

theorem finiteK3OrdinaryD_isSymm (coeff : Fin 93 → ℝ) (e f : ρ × δ) :
    (finiteK3OrdinaryD coeff e f).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  exact finiteK3Entry_symmetric coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
    ((a,Sum.inr false) : ρ × (δ ⊕ Bool)) (b,Sum.inr false)

theorem finiteK3OrdinaryO_isSymm (coeff : Fin 93 → ℝ) (e f : ρ × δ) :
    (finiteK3OrdinaryO coeff e f).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  have hab := finiteK3Ordinary_right_right coeff e f a b false true
  have hba := finiteK3Ordinary_right_right coeff e f b a true false
  have hft : (false : Bool) ≠ true := by decide
  simp only [if_neg hft, if_neg hft.symm] at hab hba
  exact (hab.symm.trans ((finiteK3Entry_symmetric coeff (e.1,Sum.inl e.2) (f.1,Sum.inl f.2)
    ((b,Sum.inr true) : ρ × (δ ⊕ Bool)) (a,Sum.inr false)).trans hba)).symm

/-- The fluctuation block is defined over the coefficient field, including ℚ. -/
def finiteK3OrdinaryH {R : Type*} [Sub R] (coeff : Fin 93 → R) (e f : ρ × δ) :
    Matrix ρ ρ R := finiteK3OrdinaryD coeff e f - finiteK3OrdinaryO coeff e f

/-- The aggregate block retains the exact division by the number of ordinary columns. -/
def finiteK3OrdinaryB {R : Type*} [Field R] (coeff : Fin 93 → R) (e f : ρ × δ)
    (ell : R) : Matrix ((ρ × δ) ⊕ ρ) ((ρ × δ) ⊕ ρ) R
  | .inl a, .inl b => finiteK3OrdinaryA coeff e f a b
  | .inl a, .inr b => finiteK3OrdinaryG coeff e f a b
  | .inr a, .inl b => finiteK3OrdinaryG coeff e f b a
  | .inr a, .inr b => finiteK3OrdinaryO coeff e f a b +
      (finiteK3OrdinaryD coeff e f a b - finiteK3OrdinaryO coeff e f a b) / ell

/-- The literal finite matrix used for aggregate certificate checks. -/
def finiteK3OrdinaryBFlat {R : Type*} [Field R] {m k : ℕ}
    (coeff : Fin 93 → R) (e f : Fin m × Fin k) (ell : R) :
    Matrix (Fin (m*k+m)) (Fin (m*k+m)) R :=
  (finiteK3OrdinaryB coeff e f ell).submatrix
    (finiteK3AggregateEquiv m k).symm (finiteK3AggregateEquiv m k).symm

/-- Delete exactly the final aggregate-row coordinate. -/
def finiteK3OrdinaryB0 {R : Type*} [Field R] {m k : ℕ}
    (coeff : Fin 93 → R) (e f : Fin m × Fin k) (ell : R) :
    Matrix (Fin (m*k+m-1)) (Fin (m*k+m-1)) R :=
  (finiteK3OrdinaryBFlat coeff e f ell).submatrix
    (Fin.castLE (Nat.sub_le (m*k+m) 1)) (Fin.castLE (Nat.sub_le (m*k+m) 1))

def finiteK3AggregateKernelFlat {R : Type*} [One R] (m k : ℕ) (ell : R) :
    Fin (m*k+m) → R := finiteK3AggregateKernel ell ∘ (finiteK3AggregateEquiv m k).symm

theorem finiteK3OrdinaryB_real (coeff : Fin 93 → ℝ) (e f : ρ × δ) (ell : ℝ) :
    finiteK3OrdinaryB coeff e f ell = ordinaryAggregateMatrix
      (finiteK3OrdinaryA coeff e f) (finiteK3OrdinaryG coeff e f)
      (finiteK3OrdinaryD coeff e f) (finiteK3OrdinaryO coeff e f) ell := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem finiteK3OrdinaryB_isSymm (coeff : Fin 93 → ℝ) (e f : ρ × δ) (ell : ℝ) :
    (finiteK3OrdinaryB coeff e f ell).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · exact (finiteK3OrdinaryA_isSymm coeff e f).apply a b
  · rfl
  · rfl
  · simp only [finiteK3OrdinaryB,
      (finiteK3OrdinaryD_isSymm coeff e f).apply a b,
      (finiteK3OrdinaryO_isSymm coeff e f).apply a b]

theorem finiteK3OrdinaryH_cast (coeff : Fin 93 → ℚ) (e f : ρ × δ) :
    (finiteK3OrdinaryH coeff e f).map (fun q : ℚ => (q : ℝ)) =
      finiteK3OrdinaryH (fun i => (coeff i : ℝ)) e f := by
  ext a b
  simp only [finiteK3OrdinaryH, Matrix.map_apply, Matrix.sub_apply, Rat.cast_sub]
  rfl

theorem finiteK3OrdinaryB_cast (coeff : Fin 93 → ℚ) (e f : ρ × δ) (ell : ℚ) :
    (finiteK3OrdinaryB coeff e f ell).map (fun q : ℚ => (q : ℝ)) =
      finiteK3OrdinaryB (fun i => (coeff i : ℝ)) e f (ell : ℝ) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · rfl
  · rfl
  · simp only [Matrix.map_apply, finiteK3OrdinaryB, Rat.cast_add, Rat.cast_div, Rat.cast_sub]
    rfl

end DittertRybin.Certificates
