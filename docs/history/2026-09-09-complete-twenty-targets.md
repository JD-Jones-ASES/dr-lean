# Completion of the twenty intended theorem targets

All twenty principal declarations in the fixed release inventory now have
actual Lean proofs. The final target is the square near-endpoint family
K=n-1 for every n>=21, with the full nonnegative probability simplex and
iff uniform equality. No permanent-floor or optimizer-shape premise is
present in its public statement. Arbitrary-rectangle P2 remains open.

The final proof adds an internally proved repeated-row Alexandrov inequality,
actual averaging on a compact two-zero doubly stochastic face, a least-norm
minimizer, and its reduced two-parameter matrix form. Two Laplace expansions
compute the actual permanent, including signed and zero-core cases. Closed
scalar bounds yield the finite and infinite quantitative permanent floors.
Those discharge the transport argument for dimensions 21–25 and from 26 onward.
The matrix reduction allows arbitrary additional zeros.

The square result is an alternative complete Dittert proof, with the earlier
public proof credited. Gurvits, Laurent–Schrijver, Pula–Song–Wanless and the
other mathematical sources retain attribution. The public probability
statements independently define actual ordered iid samples, inclusive OR,
the closed simplex, the falling-factorial uniform value, and unique equality.

## Local verification

The complete DR/Test/Solution build passed 6,196 jobs with no warnings.
Test.Axioms audited 197,437 project and public/private wrapper declarations;
only propext, Classical.choice and Quot.sound occur. The 2,736 included Lean
source hashes were unchanged across the combined replay. The independent
public Challenge compiled with exactly 20 intentional statement holes; the
Solution has no proof holes and imports no Challenge. All 47 wrapper
declarations separately passed the permitted-axiom audit.

Final boundary tests include every dimension21–25, the first tail dimension 26,
a large dimension, arbitrary zero-cell strictness, transpose, uniform equality,
and the n=2,K=1 counterexample to dropping the range guard. Signed matrix count
and zero-core tests protect the factorial and natural-subtraction identities.
The bounded-build helper's 15 graph/coverage/failure controls pass normally and
under Python optimization; a real small Lean project checked its execution.

Independent read-reviews checked all frozen matrix, scalar, transport and
public-statement interfaces. Review also exposed commented-out declarations
and multiline imports that a draft source checker did not reject. The final
checker is required to parse active declaration text and complete import
headers; source-only checks do not replace compiled proof comparison.

The final isolated source package contains 2,913 curated files
and passed 30 source/control commands with 344 local Markdown links.
The completed public source checker passed 15 checks plus five actual Lean
semantic controls. The Linux driver passed 35 static/mock controls normally
and under Python optimization. These are orchestration tests, not a kernel
replay. Documentation counts were finalized afterward; every proof, script,
configuration and metadata source byte remained unchanged.

## Release boundary

The release workflow runs the complete tracked proof closure on Linux, then
transfers a successful build to a separate independent-kernel job bound to the
same exact source commit, toolchain and archive digest. It uses pinned real
Comparator, exporter, NanoDa and Landrun, with the official sandbox adapter.
The official metadata profile runs in its exact Python/PyYAML environment.
Both kernel acceptance messages and a successful exit are required.

This record does not assert an independent CI, Comparator or NanoDa pass.
Actual outcomes belong to the exact CI run and its receipts. Public visibility
is authorized only after the entire gate passes on default-branch main.
JD retains manual Palomar submission; the Lab remains the research station.
