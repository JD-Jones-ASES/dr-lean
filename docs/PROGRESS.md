# Current formalization state

Updated 2026-09-09. Private development continues toward the complete
[twenty-target release](THEOREMS.md). Four principal targets are proved
locally: all square Dittert orders with exact equality, all rectangular K=2,
the all-order large-board bound, and its K^21 corollary. Full arbitrary-
rectangle P2 remains open.

## Completed subfamilies and certificate foundations

- [Three-row K=3](THREE-ROW-PROOF.md): every 3-by-N with N>=3 and transpose,
  including all zero supports and uniform iff equality.
- [K=3 infinite ranges](ORDER-THREE-RANGES.md): min(M,N)>=10,
  the five-through-nine-row strips, and four-row N>=960.
- [Small K=3 certificates](FINITE-K3-CERTIFICATES.md): 4-by-4 and 4-by-5
  stability bounds, plus the complete 4-by-N range 6<=N<=21. The 4-by-959
  pilot certificate is checked too.
- [Finite K=3 block soundness](FINITE-K3-BLOCK-SOUNDNESS.md): all 33
  coefficient equations, eight actual small blocks, exact aggregate kernels
  and four-pair coverage imply the original sharp probability theorem.
  Signed quartic algebra and closed-simplex uniform equality are proved.
- [Four-row K=4 analytic tail](FOUR-ROW-MINORANT.md): every N>=500 and
  transpose, using the complete corrected minorant and actual collision
  remainder. Boundary matrices and unique equality are retained.
- [Finite K=4 probability bridge](FINITE-K4-QUINTIC-BRIDGE.md): all 2,704
  physical equality patterns, 91 sparse equations, exact ten-seed host
  transport, and the actual signed quintic probability identity. Both
  four-row polynomial families and the two fixed seeds have their exact
  sharp coefficient identities. All 680 four-row Bernstein matrices and
  2,760 positive pivots are checked; final physical assembly remains.
- [Endpoint collision matrix estimate](ENDPOINT-MATRIX-INTERFACE.md): the
  exact 3/32 quadratic margin from explicit moment bounds, with signed and
  zero test vectors. Actual deletion-pattern classification, participation
  masses, local-lemma ratios and their localized expectation bound are proved.

The complete square proof has separate readable accounts for
[order three](ORDER-THREE-PROOF.md), [order four](ORDER-FOUR-PROOF.md),
[order five](ORDER-FIVE-PROOF.md), and [all orders at least six](SPECTRAL-PROOF.md).
Its van der Waerden and stability prerequisites are proved internally.
The proof is an attributed alternative to the earlier complete Dittert proof.

## Remaining work

The finite K=3 source catalogue contains all 1,330 canonical rectangles.
Their full generated replay is running in the working checkout. The present
curated checkpoint includes seventeen checked case files: sixteen for
4-by-N with 6<=N<=21, and the 4-by-959 pilot. The
[dimension manifest](../data/finite_k3_manifest.json) describes the complete
planned coverage; it is not a list of successful checks. The full dispatcher
must finish before the all-rectangle K=3 target is marked complete.

Four-row K=4 still needs its final physical matrix and kernel assembly.
The 5-by-5 and 20-by-20 K=4 seeds still need their actual matrix PSD and
constant-kernel certificates. The endpoint ranges still need rook
normalization, contender bounds and their complete parameter arguments.
The endpoint work keeps original-row and deleted-column avoidance laws
distinct. The full exact scopes and remaining
corollaries are in [THEOREMS](THEOREMS.md).

## Verification boundary

The latest curated local build passed **4,433 jobs**, with all **32,030
project declarations** audited against `propext`, `Classical.choice`, and
`Quot.sound`. It emitted no warnings; hashes of every curated Lean source
remained unchanged during the completed combined build. The closure contains
982 Lean modules. Source guards, corruption controls, normal and optimized
Python regeneration, and documentation checks passed.

Independent CI builds the exact tracked DR/Test import closure in dependency
order with at most two requested project modules per batch (491 batches
for this checkpoint). Thirteen scheduler controls pass in normal and
optimized Python. Literal K4 checks are split and serialized, including all
52-by-52 pattern gates and all 182 fixed-seed coefficient equations.
The expanded CI job has a 360-minute ceiling; this grants replay time and
does not diagnose earlier termination failures or replace any required gate.

Private main and the durable source checkout remain at independently
verified `71ab5fb1e4bae27fbd43f26ab06f2e1646750836`.
Its [main replay](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34387704231)
succeeded. Later local proofs have not yet cleared independent CI:

| Checkpoint | Independent replay status |
|---|---|
| `ce018413` full square | Cancelled; unaccepted |
| `bdd1db2f`, `486d70d7`, `2d4449e2`, `17406a61`, `f1fe2631` | Failed with exit code 143; no Lean proof error reported in the retrieved failure logs; unaccepted |
| `21b65fb5` | Cancelled; unaccepted |
| `232a8383` | Independent replay still running at this update |
| Quintic/endpoint checkpoint documented here | Local verification passed; independent CI required |

The termination cause is unconfirmed. A local build does not substitute for
independent replay, default-branch verification, or the
[full public-release gate](VERIFICATION.md). JD will submit to Palomar
manually after the complete repository passes that gate.

The detailed earlier checkpoint observations are preserved in the
[dated development record](history/2026-09-09-development.md) and the
[quintic/endpoint record](history/2026-09-09-quintic-endpoint-development.md).
Their historical status text is superseded by this page and the actual verification receipts.
