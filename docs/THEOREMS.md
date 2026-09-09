# Theorem scope and dependency order

Every target below is required for the intended complete release. The scope
comes from the audited Lab handoff and its endpoint inventory. Completed
foundation lemmas do not replace these results. All P2 targets concern
arbitrary nonnegative real matrices of mass one, include zeros, give the
sharp uniform value, and prove the unique equality case. K=1 has no general
uniqueness claim. Full P2 outside the proved ranges remains open.

The machine-readable inventory is [release-targets.json](../release-targets.json).
Its status fields are a progress record, not evidence of a theorem: compiled
statements, their actual proofs and axiom dependencies determine completion.

| Required declaration | Exact scope | Current status |
|---|---|---|
| `DittertRybin.dittert_unique_maximum` | All n>=1; nonnegative square A of total mass n; Phi(A)<=2-n!/n^n, equality exactly A_ij=1/n. | Proved locally; [square proof](ORDER-FIVE-PROOF.md) completes the last case |
| `DittertRybin.uniform_maximum_order_two` | K=2 on every M,N>=2. | Proved locally |
| `DittertRybin.uniform_maximum_order_three` | K=3 on every M,N>=3. | Pending; complete three-row family, 4-by-4 and 4-by-5, four-row N>=960, all min(M,N)>=10 and five-through-nine-row infinite strips proved; see [range map](ORDER-THREE-RANGES.md) |
| `DittertRybin.uniform_maximum_four_rows` | K=4 on every 4 by N, N>=4, and transpose. | Pending; complete analytic tail N>=500 and transpose proved on the full closed simplex; see [foundation map](RECTANGULAR-FOUNDATIONS.md) |
| `DittertRybin.uniform_maximum_five_by_five_order_four` | K=4 on the full 5 by 5 probability simplex. | Pending |
| `DittertRybin.uniform_maximum_twenty_by_twenty_order_four` | K=4 on the full 20 by 20 probability simplex. | Pending |
| `DittertRybin.uniform_maximum_large_boards` | Every K>=4 and M,N>=128(K-2)(binom(K,2)*binom(binom(K,2)^2,2)+1)^2. | Proved locally |
| `DittertRybin.uniform_maximum_large_boards_power` | Every K>=4 and min(M,N)>=K^21. | Proved locally |
| `DittertRybin.uniform_maximum_large_endpoints` | K=m on every m by N with m>=10^18 and N>=m, and transpose. | Pending |
| `DittertRybin.uniform_maximum_quadratic_endpoint_strip` | K=m, m>=96, N>=10000 m^2, and transpose. | Pending |
| `DittertRybin.uniform_maximum_quartic_endpoint_strip` | K=m, m>=16, N>=20000 m^4, and transpose. | Pending |
| `DittertRybin.uniform_maximum_combined_endpoint_strip` | K=m, m>=5, N>=10^11 m^2, and transpose. | Pending |
| `DittertRybin.uniform_maximum_consecutive_endpoint` | K=m on m by (m+1), m>=19, and transpose. | Pending |
| `DittertRybin.uniform_maximum_short_endpoint` | K=m on m by N with m>=117 and m<=N<=2m, and transpose. | Pending |
| `DittertRybin.uniform_maximum_square_near_endpoint` | K=n-1 on n by n, n>=21. | Pending |
| `DittertRybin.uniform_maximum_arithmetic_endpoint` | K=m, m>=128, m<=N<=m(m-1)/(22 log m), and transpose. | Pending |
| `DittertRybin.uniform_maximum_double_endpoint` | K=m on m by 2m for m>=80, and transpose. | Pending |
| `DittertRybin.uniform_maximum_lll_endpoint` | K=m, m>=128, 64m^(3/2)<=N<=m(m-1)/20, and transpose, when the interval is nonempty. | Pending |
| `DittertRybin.uniform_maximum_small_side` | Every 2<=K<=min(M,N) when 2<=min(M,N)<=4. | Pending |
| `DittertRybin.uniform_maximum_five_by_five` | Every 2<=K<=5 on 5 by 5. | Pending |

## Dependency order

1. **Finite probability and matrix meaning.** Ordered iid sample weights,
   inclusive-OR event, marginals, permanent, uniform evaluation, and exact
   square normalization. These definitions are visible and ordinary.
2. **Rectangular collision method.** Finite Bonferroni, witness-intersection
   bound, concentration, conditional occupation identity including the
   diagonal correction, positive blending, and compact global-maximizer
   argument. Then prove the all-order threshold and its simpler corollary.
3. **Square method.** Permanent monotonicity and block floors; a complete
   transport theorem and van der Waerden with equality; supported-cell KKT,
   entropy and finite sweep; n>=7; independently n=2,3,4,6; then n=5 using
   the earlier small cases. The dependency graph must be acyclic.
4. **Complete low orders.** The n=3 support argument, analytic strips,
   and kernel-verified polynomial certificates over whole simplexes complete
   every rectangle at K=3. The four-row K=4 proof joins n=4, the two exact
   certificate intervals and the analytic tail. Include the standalone
   5-by-5 and 20-by-20 cases and all stated equality/corollary results.
5. **Remaining endpoint ranges.** Formalize the arithmetic, entropy/cut,
   local-lemma and collision-strip arguments; keep their different domains,
   the original-row and deleted-column avoidance probabilities distinct,
   and prove their overlap inequalities rather than sampling dimensions.
6. **Release assembly.** Human-readable Challenge, exact matching Solution,
   all promised targets selected, source relationships, complete axiom audit,
   independent CI, Comparator and NanoDa. Only then change visibility.

No cited mathematical theorem may appear as a new axiom. A missing Mathlib
lemma is work to do, not permission to add its conclusion as a hypothesis
of the advertised result. The exact certificate format must have a proved
soundness bridge to an inequality on all real probability matrices.
