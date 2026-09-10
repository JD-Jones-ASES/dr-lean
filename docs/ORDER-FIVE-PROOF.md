# Order-five Dittert proof and exact certificate dependencies

The final source is `DR/Square/SpectralFive.lean`. Its principal declarations
are `dittert_order_five : DittertMaximizer 5` and
`uniformMaximizer_five_five_five : UniformMaximizer 5 5 5`.
The all-dimension wrapper is `DR/Square/AllOrders.lean`.

For a nonnegative 5-by-5 real matrix A with total mass five, write r and c
for its row and column sums, and p for its permanent. The proved bound is

$$
\Phi(A)=\prod_i r_i+\prod_j c_j-p\le 2-\frac{24}{625}
=\frac{1226}{625},
$$

with equality exactly at the matrix whose every entry is 1/5. In the
probability normalization, the equivalent sharp semimatching probability
is 29424/390625, with equality exactly at the constant 1/25 board.

## Actual maximum and balanced cut

Compactness reduces the statement to classifying every actual global
maximum on the closed simplex. The contender lemmas derive positive
marginals and the shared deficit budget

$$
\rho=1-\prod_i r_i\ge0,\quad
\sigma=1-\prod_j c_j\ge0,\quad
\rho+\sigma\le\delta=24/625-p\le24/625.
$$

Set t=sqrt(5 delta/(1-delta)), so 0<=t<9/20 and
delta=t^2/(5+t^2). `FiveMarginalBounds` derives, from the actual stationary
equations and a three-step inverse-variance bootstrap,

$$
L=1-\frac{23}{50}t\le r_i,c_j\le 1+\frac t2=H.
$$

The ten-vertex alternating sweep uses the actual stationary score and
conductance. Define q=1-t, h=H(24/625-(601/3125)t^2), d=(19/100)q-h,
and W=h(2q-h)/(2d). The rational guards prove d>0 and W<13/50 throughout
the closed certificate interval. On the physical deficit range W>=0.
The proof does not extend the physical sign of h to t=9/20.

`FiveSweepCut` shows that any nonuniform actual maximum has row and column
subsets I,J of the same size, either one or two, with actual crossing

$$
w=A(I,J^c)+A(I^c,J)\le W.
$$

`ScoreSubsetOrder` retains full marginal ordering between the chosen and
complementary subsets. Transposition, when needed, makes chosen rows the
smaller marginals and chosen columns the larger marginals. For a singleton,
this means an actual minimum row and maximum column. Ties are included.

## Singleton cut and the actual deletion minor

Let a=r_i=1-u and b=c_j=1+v. The actual extremal coordinates satisfy
u=(23/50)t x and v=(t/2)y with x,y in [0,1], including the collapsed t=0
case. The actual entry is (a+b-w)/2. For the complementary 4-by-4 minor D,
finite product-loss estimates give

$$
R_D\ge R\frac{3a-b-w}{2a^2},\qquad
C_D\ge C\frac{2L-w-a+b}{2Lb},
$$

where R and C are the whole-matrix marginal products. Both factors lie in
(0,1]. The shared budget, followed by the independently proved order-four
inequality in its homogeneous form, yields

$$
\mathrm{per}(D)\ge E(w):=
\frac{3a-b-w}{2a^2}+\frac{2L-w-a+b}{2Lb}-\delta
-\frac{61}{32}\left(\frac{10-a-b-w}{8}\right)^4.
$$

The actual retained-permutation inequality gives
p >= (a+b-w)E(w)/2. An exact derivative certificate proves E is decreasing
for 0<=w<=13/50 on the entire required marginal domain. The singleton
certificate proves

$$
p<\frac{a+b-W}{2}E(W)\le\frac{a+b-w}{2}E(w),
$$

contradicting the actual permanent floor. The last comparison also proves
the positivity of the relevant minor floor from the strict endpoint gap;
it does not assume it.

The formal chain is `FiveMinorSingletonProducts` -> `FiveMinorSingleton`
-> `SpectralFiveSingleton`. The lower-order input is the unconditional
`dittert_order_four` from `OrderFourFinal`; no certificate or order-four
inequality remains a premise of `dittert_order_five`.

## Two-by-two and three-by-three blocks

Write r(I)=2-u and c(J)=2+v. The full marginal order implies u,v>=0, and
nonnegative crossing rectangles imply u+v<=w. Put
e=(w-u-v)/2, f=(w+u+v)/2, r0=1+u/3, s0=1-v/3,
a0=1-u/2, b0=1+v/2, and L0=79/100. The four actual product factors are

$$
A_r=\frac{1-e/L_0}{r_0^3},\quad
B_c=\frac{s_0-f}{s_0^4},\quad
C_r=\frac{a_0-f}{a_0^3},\quad
D_c=\frac{1-e/L_0}{b_0^2}.
$$

Each lies in (0,1]. `FiveMinorTwoBlockProducts` derives them by finite
product loss and arithmetic-geometric mean bounds on the complementary
marginals. The shared budget and the proved orders two and three give
permanent floors X(w)-delta and Y(w)-delta, where

$$
X(w)=A_r+B_c-\frac32\left(\frac{2+(v-u-w)/2}{2}\right)^2,
$$

$$
Y(w)=C_r+D_c-\frac{16}{9}\left(\frac{3+(u-v-w)/2}{3}\right)^3.
$$

The scalar certificates prove both floors positive and their product
strictly greater than p after comparison with w0=13/50. The product of
the actual block permanents is at most p, a contradiction. This complete
actual-matrix branch is `five_two_block_cut_contradiction`; it has no
assumed scalar identity or lower-order theorem premise.

## Exact certificate method

All finite data have semantic proof bridges. The method is polynomial
identity plus Bernstein positivity on closed boxes, with rational margins.
It is not a test on sampled matrix entries.

- The guards use 67 exact coefficients; the crossing derivative uses 30;
  the two-block gaps and positive-floor checks use 500.
- The singleton literal numerator is in `SpectralFiveSingletonPolynomial`.
  `SpectralFiveSingletonBounds` identifies its evaluation with the original
  rational gap after multiplication by proved-positive denominators.
- `SparsePolynomial` proves the semantics of rational list addition,
  subtraction, multiplication and powers in every rational algebra.
  `SparseSource` interprets the literal factored numerator in that algebra.
  Eighty-six bounded arithmetic equalities identify its successive values
  with literal rational lists. These are kernel checks of the operations,
  not assumptions about externally generated data.
- The final sparse list is proved equal to the complete power tensor,
  including every zero coefficient. Its 1,049 nonzero monomials have axis
  order (t,x,y). The tensor dimensions are 37,8,7 in that axis order.
- The exact power-to-Bernstein transformations in x,y produce 56
  coefficient polynomials. Each has degree at most 36 in t. Its positive
  rational lower margin is checked on each of the nine closed intervals
  [j/20,(j+1)/20], j=0,...,8. This accounts for all 18,648 t coefficients.
- `BernsteinPositiveBlend` proves that the complete x,y blend is strictly
  positive, including every face of [0,1]^2. The global scale is explicitly
  positive. `SpectralFiveSingletonPositive` then proves the strict gap for
  all 0<=t<=9/20 and x,y in [0,1].

The finite equalities use ordinary Lean kernel reduction (`decide +kernel`)
and proved generic algebra. No native evaluation axiom, added axiom,
admitted goal, or assumed polynomial identity is part of the method.

## Attribution and verification

The proof expands the actual minors and checks the resulting polynomial
bounds inside Lean. The sparse evaluator, coefficient identities, and
finite product-loss lemmas connect those bounds to the original matrix
functional, including zero-mass minors and interval endpoints.

[SOURCES](SOURCES.md) owns attribution of the square formulation to
Cheon-Wanless, Rybin's rectangular statement, the established permanent
prerequisites, and the earlier public complete Dittert proof by Pedro Paulo
Marques do Nascimento with Hongyuan Lu's attributed small-order work.
The project claims an alternative formalized square proof, not priority
for resolving the conjecture. Novelty outside the recorded source comparison
has not been established. No peer implementation is a formal dependency.

Run `lake build Test.SpectralFive Test.AllSquareOrders` to check the
principal theorem types and their axiom audits. The tests cover sparse and
tied supports, zero deficit, zero-mass homogeneous minors, coefficient
mutation, affine interval normalization, and strict-margin transfer.
[Verification](VERIFICATION.md) describes the complete independent checks.

`AllOrders` combines the proved orders one through five with
`dittert_ge_six`. Its release declaration is
`DittertRybin.dittert_unique_maximum {n} (hn : 0 < n) : DittertMaximizer n`.
The corollary `uniform_maximum_square_endpoint` uses the proved two-way
probability normalization and includes order one. These results settle
the square endpoint within this formalization; they do not extend the
scope to all rectangles or intermediate sample orders.
