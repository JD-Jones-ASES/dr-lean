import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (0,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block04PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-18464164236012402424268144696768000000000000000 : ℚ) / 1, (323511430742348029730595125747642000000000000000 : ℚ) / 3, (-368107091661123743941803836015731475000000000000 : ℚ) / 1, (826096853820322343460919270426990001171875000000 : ℚ) / 1, (-3567054745037983739155358356388451703320312500000 : ℚ) / 3, (3009659338268185404068571950934649643164062500000 : ℚ) / 3, (-193807619673136090726940184107042159414062500000 : ℚ) / 1, (-441659040935600593097990340145540031328125000000 : ℚ) / 1, (783634514273108012140115980822891702648437500000 : ℚ) / 3, (1223499370498690261605667732313407984519531250000 : ℚ) / 3, (-482778223618481308301969296640528950055546875000 : ℚ) / 1, (30905299743016668074806151747792813584218750000 : ℚ) / 1, (283240062047280266490156616474992671005296875000 : ℚ) / 1, (-92765296788460564109039333860157283213156250000 : ℚ) / 1, (-136040760187584105436813836834204404463109375000 : ℚ) / 3, (32402314614616507816483236659774535309281250000 : ℚ) / 1, (-2612604446237309264210444705267827849600000000 : ℚ) / 3, (-10260853259090992417245811764282464445059375000 : ℚ) / 3, (1478914634717800004961481058903468766182500000 : ℚ) / 1, (226451172048792128583121123206482308311250000 : ℚ) / 3, (-259220337110195533168417427558763676572475000 : ℚ) / 3, (77625919869283448468656990672715836307100000 : ℚ) / 1, (12052786883119283612223014577747146972110000 : ℚ) / 1, (-14789902541162682823123138919464863971240000 : ℚ) / 3, (-379816586671138851545661577813650953800000 : ℚ) / 3, (624364622337233654673363506700857008525000 : ℚ) / 3, (-5645128833297646123432470528246687375000 : ℚ) / 1, (-6726009369137529148334282414435376395000 : ℚ) / 3, (924042698144781542041397513608697345000 : ℚ) / 1, (241982053337847469449049318364932225000 : ℚ) / 3, (-6677459412537247416058210283086175000 : ℚ) / 1, (3031609350017932697283918607193675000 : ℚ) / 3, (898214523019253574605070015716095000 : ℚ) / 3, (43129298600089420074982485097015000 : ℚ) / 3, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block04Margin0 : ℚ := (39215843339115210991725436844264056721056748814836558902532548308521146792956399779261 : ℚ) / 34359738368000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_0 : ∀ i : Fin 37, block04Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block04PowerCoefficients
      block04Margin0 (by norm_num) block04_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin1 : ℚ := (1543400187672290463630294336759903725536636189064580658269210902307165590031 : ℚ) / 2000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_1 : ∀ i : Fin 37, block04Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block04PowerCoefficients
      block04Margin1 (by norm_num) block04_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin2 : ℚ := (20252249137115186429064480850646942205389461300330369785582814027490252397823970594349 : ℚ) / 34359738368000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_2 : ∀ i : Fin 37, block04Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block04PowerCoefficients
      block04Margin2 (by norm_num) block04_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin3 : ℚ := (478680132493632043060302492023722389140970866914070001310105775328 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_3 : ∀ i : Fin 37, block04Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block04PowerCoefficients
      block04Margin3 (by norm_num) block04_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin4 : ℚ := (3765112960515041114796769108140458092503972269143822626152648853413439 : ℚ) / 7528118620870672384000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_4 : ∀ i : Fin 37, block04Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block04PowerCoefficients
      block04Margin4 (by norm_num) block04_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin5 : ℚ := (18508897268421164088800191930342447522059969007946672386754908125 : ℚ) / 36893488147419103232

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_5 : ∀ i : Fin 37, block04Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block04PowerCoefficients
      block04Margin5 (by norm_num) block04_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin6 : ℚ := (1064321174378933335491505423632483076908645489227751154504893984974877184059 : ℚ) / 2000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_6 : ∀ i : Fin 37, block04Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block04PowerCoefficients
      block04Margin6 (by norm_num) block04_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin7 : ℚ := (20630607558795021212550929430684084750631982869850838848660035569998444356829861783269 : ℚ) / 34359738368000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_7 : ∀ i : Fin 37, block04Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block04PowerCoefficients
      block04Margin7 (by norm_num) block04_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block04Margin8 : ℚ := (664445115409418442450643604794513608446544277977995592950571251712 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block04_coefficient_bound_8 : ∀ i : Fin 37, block04Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block04PowerCoefficients) i := by
  decide +kernel

theorem block04_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block04Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block04PowerCoefficients
      block04Margin8 (by norm_num) block04_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block04_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block04PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block04_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block04_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block04_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block04_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block04_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block04_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block04_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block04_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block04_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
