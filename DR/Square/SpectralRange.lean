import DR.Square.SpectralSix
import DR.Square.SpectralSeven

/-! The completed square spectral range on the full closed simplex. -/

namespace DittertRybin

theorem dittert_ge_six {n : ℕ} (hn : 6 ≤ n) : DittertMaximizer n := by
  obtain h | h := eq_or_lt_of_le hn
  · subst n; exact dittert_order_six
  · exact dittert_ge_seven (by omega)

end DittertRybin
