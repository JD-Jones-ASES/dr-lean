import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (4,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block30PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-159865493340885840690118235249920000000000000000 : ℚ) / 7, (2892535063702839400381669300475353400000000000000 : ℚ) / 21, (-3299648317008745188383247878845663587600000000000 : ℚ) / 7, (21204653662115531871773368705299951649184375000000 : ℚ) / 21, (-26156622565760637792269770547626749094718593750000 : ℚ) / 21, (8422049935099072777350368121645693792695468750000 : ℚ) / 21, (1533713452359480080288933751431124920261289062500 : ℚ) / 1, (-61951285419851293396597892794012213835917226562500 : ℚ) / 21, (6615351247109220426988940673873118694589382812500 : ℚ) / 3, (3233101371981048625885991828445037578829273437500 : ℚ) / 21, (-4738599447360495326025049661259049723377723437500 : ℚ) / 3, (21661593497450734817183687503658735248743100000000 : ℚ) / 21, (875558485996225002075101434122872522558512875000 : ℚ) / 7, (-1188485172840711071548059163252220985050838500000 : ℚ) / 3, (103260952983185163351226849060114771419722287500 : ℚ) / 1, (119501339114087005558379516353523966021844987500 : ℚ) / 3, (-599644679098701594788866583177724699095393387500 : ℚ) / 21, (102368846586785094798290649416740899125017362500 : ℚ) / 21, (16955335283111799112400172248871192290386978750 : ℚ) / 7, (-28725166712410120468386072259765518853954926250 : ℚ) / 21, (2221574314389469791774036922066139500693627000 : ℚ) / 21, (894539552970261156610138799970304601124161500 : ℚ) / 7, (-178680433919133248590006181331857823941728890 : ℚ) / 7, (-92726089179458161931606890142467849330805720 : ℚ) / 21, (4213545862382114011065122552798010594016108 : ℚ) / 3, (-610499442766815445568808180769615046461648 : ℚ) / 7, (-957280070859957251814124199841679455188840 : ℚ) / 21, (157373937840900924887055974210546885318050 : ℚ) / 21, (1958902729556295641571565425073809543910 : ℚ) / 7, (-4983224048384607205105268783621630647874 : ℚ) / 21, (239162124439510618045768901529646538926 : ℚ) / 21, (3359146593738607859264703560621457730 : ℚ) / 1, (-358641643507652232033231031393636920 : ℚ) / 1, (-130544277693183136955543574700118710 : ℚ) / 7, (46027587466015429104021308095534408 : ℚ) / 7, (9126159583778921287866293846528374 : ℚ) / 21]

def block30Margin0 : ℚ := (237057765804346381244921872702315006536945917293715464133761987329156276816754827236905596809 : ℚ) / 240518168576000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_0 : ∀ i : Fin 37, block30Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block30PowerCoefficients
      block30Margin0 (by norm_num) block30_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin1 : ℚ := (1915989741011098527154440335046418466696490794924454867284914658552578969123921269 : ℚ) / 3500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_1 : ∀ i : Fin 37, block30Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block30PowerCoefficients
      block30Margin1 (by norm_num) block30_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin2 : ℚ := (11744952798355968794841712261692921033909846033986260367120657710102068807468794851056899967 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_2 : ∀ i : Fin 37, block30Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block30PowerCoefficients
      block30Margin2 (by norm_num) block30_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin3 : ℚ := (26791115784433937347077539283458427599707894101647753822148696637358748 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_3 : ∀ i : Fin 37, block30Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block30PowerCoefficients
      block30Margin3 (by norm_num) block30_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin4 : ℚ := (4829785446507276666099904574245092405318165695494565382558686184772473248059 : ℚ) / 19267278595290877132800000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_4 : ∀ i : Fin 37, block30Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block30PowerCoefficients
      block30Margin4 (by norm_num) block30_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin5 : ℚ := (596977704778889049501405932738012022377179415154751052481140960175 : ℚ) / 2361183241434822606848

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_5 : ∀ i : Fin 37, block30Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block30PowerCoefficients
      block30Margin5 (by norm_num) block30_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin6 : ℚ := (989385955467756823660698461937032501013983786002659453046073785794783240056575989 : ℚ) / 3500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_6 : ∀ i : Fin 37, block30Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block30PowerCoefficients
      block30Margin6 (by norm_num) block30_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin7 : ℚ := (11759475114081668534492496428927896647750957888961023436475029333292074375781393261353704367 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_7 : ∀ i : Fin 37, block30Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block30PowerCoefficients
      block30Margin7 (by norm_num) block30_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block30Margin8 : ℚ := (44156528409887907649876844606233135102534165993528788383698822744823808 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block30_coefficient_bound_8 : ∀ i : Fin 37, block30Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block30PowerCoefficients) i := by
  decide +kernel

theorem block30_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block30Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block30PowerCoefficients
      block30Margin8 (by norm_num) block30_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block30_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block30PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block30_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block30_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block30_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block30_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block30_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block30_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block30_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block30_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block30_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
