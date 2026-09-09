import DR.Certificates.FourByFiveThreeDefinitions
import DR.Certificates.PairNormalization

/-! Actual row/column permutations cover every physical multiplier pair. -/
namespace DittertRybin.Certificates

def fourByFiveThreePairType (e f : Fin 20) : Fin 4 :=
  if (fourByFiveThreeCell.symm e).1=(fourByFiveThreeCell.symm f).1 then
    (if (fourByFiveThreeCell.symm e).2=(fourByFiveThreeCell.symm f).2 then 0 else 1)
  else (if (fourByFiveThreeCell.symm e).2=(fourByFiveThreeCell.symm f).2 then 2 else 3)

def fourByFiveThreePairPermutation (e f : Fin 20) : Equiv.Perm (Fin 20) :=
  fourByFiveThreeCell.symm.trans
    ((Equiv.prodCongr
      (pairNormalization 0 1 (fourByFiveThreeCell.symm e).1 (fourByFiveThreeCell.symm f).1)
      (pairNormalization 0 1 (fourByFiveThreeCell.symm e).2 (fourByFiveThreeCell.symm f).2)).trans
        fourByFiveThreeCell)

theorem fourByFiveThreePairPermutation_first (e f : Fin 20) :
    fourByFiveThreePairPermutation e f e=0 := by
  simp only [fourByFiveThreePairPermutation,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply',
    pairNormalization_first (0:Fin 4) 1 _ _ (by decide),
    pairNormalization_first (0:Fin 5) 1 _ _ (by decide)]
  rfl

theorem fourByFiveThreePairPermutation_second (e f : Fin 20) :
    fourByFiveThreePairPermutation e f f=fourByFiveThreeMultiplier (fourByFiveThreePairType e f) := by
  simp only [fourByFiveThreePairPermutation,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply',
    pairNormalization_second]
  by_cases hr : (fourByFiveThreeCell.symm e).1=(fourByFiveThreeCell.symm f).1 <;>
    by_cases hc : (fourByFiveThreeCell.symm e).2=(fourByFiveThreeCell.symm f).2 <;>
    simp only [fourByFiveThreePairType,hr,hc,if_true,if_false,fourByFiveThreeMultiplier]
  all_goals norm_num [fourByFiveThreeCell,finProdFinEquiv,Matrix.cons_val_two,Matrix.cons_val_three,Fin.ext_iff]

theorem fourByFiveThreeMatrix_conjugate (e f : Fin 20) :
    fourByFiveThreeMatrix e f=(fourByFiveThreeSeed (fourByFiveThreePairType e f)).submatrix
      (fourByFiveThreePairPermutation e f) (fourByFiveThreePairPermutation e f) := by
  let r := pairNormalization 0 1 (fourByFiveThreeCell.symm e).1 (fourByFiveThreeCell.symm f).1
  let c := pairNormalization 0 1 (fourByFiveThreeCell.symm e).2 (fourByFiveThreeCell.symm f).2
  have hmap (a : Fin 20) : fourByFiveThreeCell.symm (fourByFiveThreePairPermutation e f a)=
      (r (fourByFiveThreeCell.symm a).1,c (fourByFiveThreeCell.symm a).2) := by
    simp [fourByFiveThreePairPermutation,r,c,Prod.map_apply']
  have he := hmap e
  have hf := hmap f
  rw [fourByFiveThreePairPermutation_first] at he
  rw [fourByFiveThreePairPermutation_second] at hf
  ext a b
  change finiteK3Entry fourByFiveThreeCoefficient (fourByFiveThreeCell.symm e) (fourByFiveThreeCell.symm f)
      (fourByFiveThreeCell.symm a) (fourByFiveThreeCell.symm b)=
    finiteK3Entry fourByFiveThreeCoefficient (fourByFiveThreeCell.symm 0)
      (fourByFiveThreeCell.symm (fourByFiveThreeMultiplier (fourByFiveThreePairType e f)))
      (fourByFiveThreeCell.symm (fourByFiveThreePairPermutation e f a))
      (fourByFiveThreeCell.symm (fourByFiveThreePairPermutation e f b))
  rw [he,hf,hmap a,hmap b]
  exact (finiteK3Entry_map _ r c r.injective c.injective _ _ _ _).symm

end DittertRybin.Certificates
