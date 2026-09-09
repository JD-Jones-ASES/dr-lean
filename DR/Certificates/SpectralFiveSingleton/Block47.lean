import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (6,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block47PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-165898383706671670940080280000992000000000000000 : ℚ) / 7, (2930300024904427231441609206779338280000000000000 : ℚ) / 21, (-9825593130078298884819739777763186632000000000000 : ℚ) / 21, (20844825582269943080890047201431939912875000000000 : ℚ) / 21, (-3839641499094443724973591433418751480793750000000 : ℚ) / 3, (5236741900039141671634155298822715054359375000000 : ℚ) / 7, (3083063272145783208410246997214506945410937500000 : ℚ) / 7, (-6606802070561792581834015019033634657944531250000 : ℚ) / 7, (-933716611452110488160196699135715237142500000000 : ℚ) / 7, (35421458316928023095123540905802447743063437500000 : ℚ) / 21, (-1701473295262540132957238561885857491023812500000 : ℚ) / 1, (1811837531289179588932184682164952590275275000000 : ℚ) / 7, (15865434837870487171940392905401854618323088750000 : ℚ) / 21, (-10814048665634768194614346510162118732488022500000 : ℚ) / 21, (-710927250183200795674811603191436975955982250000 : ℚ) / 21, (2326620906636522843292331921545790143839193750000 : ℚ) / 21, (-960928613269483847420235560051589575079035500000 : ℚ) / 21, (-47123082397825539703466377600563997727543000000 : ℚ) / 21, (210605826291126138451856201276011648296750387500 : ℚ) / 21, (-43707117089251455257584000659732563760904512500 : ℚ) / 21, (-11173309031456223031356404697815874293691395000 : ℚ) / 21, (7510525983162022032079382036638578562366117000 : ℚ) / 21, (-140758415674299270736265457587829916309499100 : ℚ) / 7, (-122496016377460310211471238465407251091893950 : ℚ) / 7, (97721696335216475050936481275536772743218140 : ℚ) / 21, (547865419771782997060811636875605980758600 : ℚ) / 7, (-4208194296202092784978789354071306464868050 : ℚ) / 21, (602193686534943804522119505119906230207925 : ℚ) / 21, (3511959058516094883706668949285579501925 : ℚ) / 1, (-980926587731876445657675496529401726885 : ℚ) / 1, (365675056262613504606613697752779273525 : ℚ) / 7, (155987140419278424749421005905430641450 : ℚ) / 7, (-24833842973276037944962437737004672025 : ℚ) / 21, (-368199702003047915087887702908802075 : ℚ) / 6, (856073447913174899068327346690650735 : ℚ) / 21, (114076994797236516098328673081604675 : ℚ) / 42]

def block47Margin0 : ℚ := (5208056255133322203441550625525038584186284783481300534511557663381217202779352209466478903 : ℚ) / 5497558138880000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_0 : ∀ i : Fin 37, block47Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block47PowerCoefficients
      block47Margin0 (by norm_num) block47_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin1 : ℚ := (10772532220810342833369370601413784381060725180594703718540901425961744388437929 : ℚ) / 22400000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_1 : ∀ i : Fin 37, block47Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block47PowerCoefficients
      block47Margin1 (by norm_num) block47_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin2 : ℚ := (1407567521389199410574288018778768934198567022685556209711723960371664350918342423206473879 : ℚ) / 5497558138880000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_2 : ∀ i : Fin 37, block47Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block47PowerCoefficients
      block47Margin2 (by norm_num) block47_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin3 : ℚ := (95708921685351973393722928084678155804413812108000259623733526553743 : ℚ) / 582076609134674072265625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_3 : ∀ i : Fin 37, block47Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block47PowerCoefficients
      block47Margin3 (by norm_num) block47_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin4 : ℚ := (122281271795421205573221611868566400964436727484422594951812550716889 : ℚ) / 845137579737003107287040

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_4 : ∀ i : Fin 37, block47Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block47PowerCoefficients
      block47Margin4 (by norm_num) block47_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin5 : ℚ := (9584906606938048559407257413617662663544088868010873973668821899385 : ℚ) / 66113130760175032991744

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_5 : ∀ i : Fin 37, block47Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block47PowerCoefficients
      block47Margin5 (by norm_num) block47_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin6 : ℚ := (93018759595923039752556244187903282841603951310975881806142342992977149774047481 : ℚ) / 560000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_6 : ∀ i : Fin 37, block47Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block47PowerCoefficients
      block47Margin6 (by norm_num) block47_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin7 : ℚ := (235795080943603587456419347200852415568603638594145700348903480152541665272317344499071931 : ℚ) / 1099511627776000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_7 : ∀ i : Fin 37, block47Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block47PowerCoefficients
      block47Margin7 (by norm_num) block47_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block47Margin8 : ℚ := (167877307447073070386505391581167810646298920132045330502791014940672 : ℚ) / 582076609134674072265625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block47_coefficient_bound_8 : ∀ i : Fin 37, block47Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block47PowerCoefficients) i := by
  decide +kernel

theorem block47_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block47Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block47PowerCoefficients
      block47Margin8 (by norm_num) block47_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block47_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block47PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block47_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block47_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block47_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block47_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block47_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block47_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block47_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block47_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block47_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
