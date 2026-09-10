import DR.Endpoint.AllAspectParameters
import DR.Endpoint.Arithmetic
import DR.Endpoint.LLLStrip
import DR.Endpoint.Transition
import DR.Endpoint.Quadratic

/-! Every aspect ratio once the smaller dimension is at least10^18.
The actual arithmetic, local-lemma, transition and quadratic theorems
cover four overlapping intervals, with the remaining overlap proved
for all integer dimensions in AllAspectParameters. -/
namespace DittertRybin

theorem uniform_maximum_large_endpoints {m n : ℕ} (hm : 10^18≤m) (hmn : m≤n) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  by_cases hquadratic : 10000*m^2≤n
  · exact uniform_maximum_quadratic_endpoint_strip (by omega) hquadratic
  by_cases htransition : m*(m-1)≤20*n
  · exact uniform_maximum_transition_endpoint hm hmn htransition (by omega)
  by_cases hlll : 4096*m^3≤n^2
  · exact uniform_maximum_lll_endpoint (by omega) hmn hlll (by omega)
  exact uniform_maximum_arithmetic_endpoint (by omega) hmn
    (endpoint_arithmetic_lll_overlap hm hmn (by omega))

end DittertRybin
