import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (5,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block36PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-168678989447912306821448361647456000000000000000 : ℚ) / 7, (445553720659406751020810631214364600000000000000 : ℚ) / 3, (-3621110108494522855552882985677473771000000000000 : ℚ) / 7, (70798862321839947516941248555990177157140625000000 : ℚ) / 63, (-88204204321285932128314871115186356013778515625000 : ℚ) / 63, (26047838237890521026212106782233378906838281250000 : ℚ) / 63, (40781090469402137976951844586599993037752050781250 : ℚ) / 21, (-242379423000757780597482627985029656389196386718750 : ℚ) / 63, (66952334447764974681687333960080983853796542968750 : ℚ) / 21, (-20013098141390050982035171775377574942661777343750 : ℚ) / 63, (-5365360575364739065171070296988900120514441406250 : ℚ) / 3, (93145487077063916251894764205892675131135421875000 : ℚ) / 63, (-5594201791639502388624070031792252172361955312500 : ℚ) / 63, (-3147952818252027008607254297390522249367401250000 : ℚ) / 7, (11896212585958969194275504910561578032163601906250 : ℚ) / 63, (137409376464351691583765297949463106558127718750 : ℚ) / 7, (-2343349495923095622668325013308198960888651781250 : ℚ) / 63, (95660493652439746690988049554495176600857718750 : ℚ) / 9, (33625170247341514886139685612649965907683878125 : ℚ) / 21, (-12908384512724387027213013812846068324973059375 : ℚ) / 7, (6553417701383197308607559987501982658036032500 : ℚ) / 21, (7200144599093806019101285231154010358239563750 : ℚ) / 63, (-825333151675985090840013766284337840344466325 : ℚ) / 21, (-6279067080865754236126590845598206390954900 : ℚ) / 9, (102131253463830794346046180357211702169437530 : ℚ) / 63, (-4879160317550516246542432506027479647999720 : ℚ) / 21, (-1450908883532272141366432004130175978647650 : ℚ) / 63, (91084473219994110383793674902918645413025 : ℚ) / 9, (-9732463607262372219612086838122670178925 : ℚ) / 21, (-10203270709308636377922727234088068848145 : ℚ) / 63, (640517247440582221140898188901847464805 : ℚ) / 21, (136906506006031490146750564676914536925 : ℚ) / 63, (-6273021786177872252759082657470674900 : ℚ) / 21, (1872516626396536203221355831440198375 : ℚ) / 63, (531697993141902370684384076276000920 : ℚ) / 63, (22815398959447303219665734616320935 : ℚ) / 63]

def block36Margin0 : ℚ := (272611697495761031156325903414854546220533027597938733057243848369885059211873494136984939289 : ℚ) / 288621802291200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_0 : ∀ i : Fin 37, block36Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block36PowerCoefficients
      block36Margin0 (by norm_num) block36_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin1 : ℚ := (98656305196544516003706567772474370930402852856998846947036806860406727827895929 : ℚ) / 200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_1 : ∀ i : Fin 37, block36Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block36PowerCoefficients
      block36Margin1 (by norm_num) block36_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin2 : ℚ := (3946236339712721350308520743096075759533624856040921278697207366246727282982425595413374149 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_2 : ∀ i : Fin 37, block36Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block36PowerCoefficients
      block36Margin2 (by norm_num) block36_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin3 : ℚ := (4321888285686912433967896421752981758588067005241739676352682132890498 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_3 : ∀ i : Fin 37, block36Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block36PowerCoefficients
      block36Margin3 (by norm_num) block36_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin4 : ℚ := (6938679502851117801651576467721865111144030494723852868018226273372550975157 : ℚ) / 34240441871782379520000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_4 : ∀ i : Fin 37, block36Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block36PowerCoefficients
      block36Margin4 (by norm_num) block36_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin5 : ℚ := (974118518462648999637416030641141087850080587277809187422580648905 : ℚ) / 4722366482869645213696

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_5 : ∀ i : Fin 37, block36Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block36PowerCoefficients
      block36Margin5 (by norm_num) block36_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin6 : ℚ := (334925923185177800269574964944851846607855774520169483590710607892104594716564223 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_6 : ∀ i : Fin 37, block36Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block36PowerCoefficients
      block36Margin6 (by norm_num) block36_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin7 : ℚ := (12366922584879531518120182326120297792548744987572888042337627244316872438177231566269565887 : ℚ) / 41231686041600000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_7 : ∀ i : Fin 37, block36Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block36PowerCoefficients
      block36Margin7 (by norm_num) block36_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block36Margin8 : ℚ := (7941704123861692627260318114329896429181389174389909461177353093874688 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block36_coefficient_bound_8 : ∀ i : Fin 37, block36Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block36PowerCoefficients) i := by
  decide +kernel

theorem block36_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block36Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block36PowerCoefficients
      block36Margin8 (by norm_num) block36_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block36_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block36PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block36_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block36_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block36_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block36_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block36_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block36_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block36_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block36_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block36_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
