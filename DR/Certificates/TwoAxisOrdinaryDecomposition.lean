import DR.Certificates.TwoAxisOrdinaryBlocks

/-! Exact iteration of the ordinary-axis decomposition on the physical product. -/
namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section
variable {α β ρ γ : Type*}

theorem ordinaryPairAverage_swap (R : ℝ) (f : OrdinaryPair α → ℝ)
    (p q : α ⊕ Unit) :
    ordinaryPairAverage R f q p =
      ordinaryPairAverage R (fun r => f r.swap) p q := by
  cases p <;> cases q <;> rfl

theorem ordinaryPairAverage_sub (R : ℝ) (f g : OrdinaryPair α → ℝ)
    (p q : α ⊕ Unit) :
    ordinaryPairAverage R (fun r => f r-g r) p q =
      ordinaryPairAverage R f p q - ordinaryPairAverage R g p q := by
  cases p <;> cases q <;> simp only [ordinaryPairAverage]
  all_goals ring

def ordinaryScalarAggregateVector [Fintype ρ]
    (p : α ⊕ ρ → ℝ) : α ⊕ Unit → ℝ
  | .inl i => p (.inl i)
  | .inr _ => ∑ r, p (.inr r)

def ordinaryScalarFluctuation [Fintype ρ]
    (p : α ⊕ ρ → ℝ) (r : ρ) : ℝ :=
  p (.inr r) - (∑ s, p (.inr s))/(Fintype.card ρ : ℝ)

theorem quadraticValue_ordinaryScalar_decomposition
    [Fintype α] [Fintype ρ] [DecidableEq ρ]
    (f : OrdinaryPair α → ℝ) (hf : ∀ r, f r.swap = f r)
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (p : α ⊕ ρ → ℝ) :
    quadraticValue (fun i j => f (ordinaryPair i j)) p =
      quadraticValue (ordinaryPairAverage (Fintype.card ρ) f) (ordinaryScalarAggregateVector p) +
      ∑ r, (f .same-f .different)*(ordinaryScalarFluctuation p r)^2 := by
  let K : OrdinaryPair α → Matrix Unit Unit ℝ := fun r => Matrix.of (fun _ _ => f r)
  have hK : OrdinaryPairMatrixSymm K := fun r _ _ => hf r
  have h := quadraticValue_ordinaryPair_decomposition K hK hR (fun q => p q.1)
  have ha : ordinaryPairAggregateVector (fun q : (α ⊕ ρ) × Unit => p q.1) =
      fun q => ordinaryScalarAggregateVector p q.1 := by
    funext q
    rcases q with ⟨i,j⟩
    cases i <;> rfl
  rw [ha] at h
  have hd : K .same-K .different = Matrix.of (fun _ _ => f .same-f .different) := rfl
  rw [hd] at h
  simpa only [K,Matrix.of_apply,quadraticValue,ordinaryPairMatrix,ordinaryPairAggregate,
    ordinaryPairFluctuation,
    ordinaryScalarFluctuation,Fintype.sum_prod_type,Fintype.sum_unique,Matrix.sub_apply,
    Pi.sub_apply,pow_two,mul_comm,mul_left_comm,mul_assoc] using h

def ordinaryColumnPairMatrix [DecidableEq γ] (K : OrdinaryPair β → Matrix α α ℝ) :
    Matrix (α × (β ⊕ γ)) (α × (β ⊕ γ)) ℝ :=
  fun p q => K (ordinaryPair p.2 q.2) p.1 q.1

def ordinaryColumnPairAggregate (K : OrdinaryPair β → Matrix α α ℝ) (C : ℝ) :
    Matrix (α × (β ⊕ Unit)) (α × (β ⊕ Unit)) ℝ :=
  fun p q => ordinaryPairAverage C (fun c => K c p.1 q.1) p.2 q.2

def ordinaryColumnAggregateVector [Fintype γ]
    (p : α × (β ⊕ γ) → ℝ) : α × (β ⊕ Unit) → ℝ
  | (i,.inl j) => p (i,.inl j)
  | (i,.inr _) => ∑ c, p (i,.inr c)

def ordinaryColumnFluctuation [Fintype γ]
    (p : α × (β ⊕ γ) → ℝ) (c : γ) (i : α) : ℝ :=
  p (i,.inr c)-(∑ d, p (i,.inr d))/(Fintype.card γ : ℝ)

theorem quadraticValue_ordinaryColumnPair_decomposition
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (K : OrdinaryPair β → Matrix α α ℝ) (hK : OrdinaryPairMatrixSymm K)
    (hC : (Fintype.card γ : ℝ) ≠ 0) (p : α × (β ⊕ γ) → ℝ) :
    quadraticValue (ordinaryColumnPairMatrix K) p =
      quadraticValue (ordinaryColumnPairAggregate K (Fintype.card γ))
        (ordinaryColumnAggregateVector p) +
      ∑ c, quadraticValue (K .same-K .different) (ordinaryColumnFluctuation p c) := by
  have h := quadraticValue_ordinaryPair_decomposition K hK hC (fun q => p (q.2,q.1))
  have he : ordinaryColumnPairMatrix (γ := γ) K =
      (ordinaryPairMatrix K).submatrix (Equiv.prodComm α (β ⊕ γ)) (Equiv.prodComm α (β ⊕ γ)) := rfl
  have ha : ordinaryColumnPairAggregate K (Fintype.card γ) =
      (ordinaryPairAggregate K (Fintype.card γ)).submatrix
        (Equiv.prodComm α (β ⊕ Unit)) (Equiv.prodComm α (β ⊕ Unit)) := rfl
  have hp : (fun i => ordinaryColumnAggregateVector p ((Equiv.prodComm α (β ⊕ Unit)).symm i)) =
      ordinaryPairAggregateVector (fun q => p (q.2,q.1)) := by
    funext q
    rcases q with ⟨q,i⟩
    cases q <;> rfl
  rw [he,ha,quadraticValue_submatrix_equiv,quadraticValue_submatrix_equiv]
  rw [hp]
  exact h

def twoAxisRowFamily [DecidableEq γ]
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) :
    OrdinaryPair α → Matrix (β ⊕ γ) (β ⊕ γ) ℝ :=
  fun r i j => K r (ordinaryPair i j)

theorem twoAxisRowFamily_symm [DecidableEq γ]
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K) :
    OrdinaryPairMatrixSymm (twoAxisRowFamily (γ := γ) K) := by
  intro r i j
  change K r.swap (ordinaryPair j i) = K r (ordinaryPair i j)
  rw [ordinaryPair_swap i j]
  exact hK _ _

def twoAxisColumnAveragedFamily (K : OrdinaryPair α → OrdinaryPair β → ℝ) (R : ℝ) :
    OrdinaryPair β → Matrix (α ⊕ Unit) (α ⊕ Unit) ℝ :=
  fun c => ordinaryPairAverage R (fun r => K r c)

theorem twoAxisColumnAveragedFamily_symm
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K) (R : ℝ) :
    OrdinaryPairMatrixSymm (twoAxisColumnAveragedFamily K R) := by
  intro c i j
  change ordinaryPairAverage R (fun r => K r c.swap) j i =
    ordinaryPairAverage R (fun r => K r c) i j
  rw [ordinaryPairAverage_swap]
  have hf : (fun r => K r.swap c.swap) = fun r => K r c := funext fun r => hK r c
  rw [hf]

theorem twoAxisColumnAveragedFamily_aggregate
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (R C : ℝ) :
    ordinaryColumnPairAggregate (twoAxisColumnAveragedFamily K R) C =
      twoAxisTrivialMatrix K R C := by
  ext p q
  exact (twoAxisTrivialMatrix_averages_commute K R C p q).symm

theorem twoAxisColumnAveragedFamily_standard
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (R : ℝ) :
    twoAxisColumnAveragedFamily K R .same-twoAxisColumnAveragedFamily K R .different =
      twoAxisColumnStandardMatrix K R := by
  ext p q
  exact (ordinaryPairAverage_sub R _ _ p q).symm

def twoAxisAggregateVector [Fintype ρ] [Fintype γ]
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) : (α ⊕ Unit) × (β ⊕ Unit) → ℝ :=
  ordinaryColumnAggregateVector (ordinaryPairAggregateVector p)

def twoAxisRowFluctuationAggregate [Fintype ρ] [Fintype γ]
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (r : ρ) : β ⊕ Unit → ℝ :=
  ordinaryScalarAggregateVector (ordinaryPairFluctuation p r)

def twoAxisColumnFluctuationAggregate [Fintype ρ] [Fintype γ]
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (c : γ) : α ⊕ Unit → ℝ :=
  ordinaryColumnFluctuation (ordinaryPairAggregateVector p) c

def twoAxisInteractionFluctuation [Fintype ρ] [Fintype γ]
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (r : ρ) (c : γ) : ℝ :=
  ordinaryScalarFluctuation (ordinaryPairFluctuation p r) c

/-- Exact four-sector decomposition on all signed physical vectors. -/
theorem quadraticValue_twoAxis_decomposition
    [Fintype α] [Fintype β] [Fintype ρ] [Fintype γ] [DecidableEq ρ] [DecidableEq γ]
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K)
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (hC : (Fintype.card γ : ℝ) ≠ 0)
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) :
    quadraticValue (twoAxisOrdinaryMatrix K) p =
      quadraticValue (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ))
        (twoAxisAggregateVector p) +
      (∑ c, quadraticValue (twoAxisColumnStandardMatrix K (Fintype.card ρ))
        (twoAxisColumnFluctuationAggregate p c)) +
      (∑ r, quadraticValue (twoAxisRowStandardMatrix K (Fintype.card γ))
        (twoAxisRowFluctuationAggregate p r)) +
      ∑ r, ∑ c, twoAxisInteraction K*(twoAxisInteractionFluctuation p r c)^2 := by
  have hr := quadraticValue_ordinaryPair_decomposition (twoAxisRowFamily K)
    (twoAxisRowFamily_symm K hK) hR p
  have hmid : ordinaryPairAggregate (twoAxisRowFamily (γ := γ) K) (Fintype.card ρ) =
      ordinaryColumnPairMatrix (twoAxisColumnAveragedFamily K (Fintype.card ρ)) := rfl
  have hc := quadraticValue_ordinaryColumnPair_decomposition
    (twoAxisColumnAveragedFamily K (Fintype.card ρ))
    (twoAxisColumnAveragedFamily_symm K hK _) hC (ordinaryPairAggregateVector p)
  have hs (r : ρ) : quadraticValue
      (twoAxisRowFamily (γ := γ) K .same-twoAxisRowFamily K .different)
      (ordinaryPairFluctuation p r) =
      quadraticValue (twoAxisRowStandardMatrix K (Fintype.card γ))
        (twoAxisRowFluctuationAggregate p r) +
      ∑ c, twoAxisInteraction K*(twoAxisInteractionFluctuation p r c)^2 := by
    have hf (c : OrdinaryPair β) :
        K .same c.swap-K .different c.swap = K .same c-K .different c :=
      congrArg₂ (fun x y : ℝ => x-y) (hK .same c) (hK .different c)
    have hh := quadraticValue_ordinaryScalar_decomposition
      (fun c => K .same c-K .different c) hf hC (ordinaryPairFluctuation p r)
    have hi : (K .same .same-K .different .same) -
        (K .same .different-K .different .different) = twoAxisInteraction K := by
      unfold twoAxisInteraction
      ring
    rw [hi] at hh
    exact hh
  change quadraticValue (twoAxisOrdinaryMatrix K) p = _ at hr
  rw [hr,hmid,hc,twoAxisColumnAveragedFamily_aggregate,twoAxisColumnAveragedFamily_standard]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  simp only [twoAxisAggregateVector,twoAxisColumnFluctuationAggregate,add_assoc]

theorem twoAxisAggregateVector_constant [Fintype ρ] [Fintype γ]
    (t : ℝ) (q : (α ⊕ Unit) × (β ⊕ Unit)) :
    twoAxisAggregateVector (ρ := ρ) (γ := γ) (fun _ => t) q =
      t*twoAxisAggregateWeight (Fintype.card ρ) (Fintype.card γ) q := by
  rcases q with ⟨i,j⟩
  cases i <;> cases j <;>
    simp only [twoAxisAggregateVector,ordinaryColumnAggregateVector,
      ordinaryPairAggregateVector,twoAxisAggregateWeight,ordinaryAxisWeight,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  all_goals ring

end
end DittertRybin.Certificates
