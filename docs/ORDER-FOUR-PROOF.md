# Order four: an exact polynomial certificate

For every nonnegative 4-by-4 matrix of mass four, the Dittert functional
is at most 61/32, with equality exactly when every entry is 1/4.
`DittertRybin.dittert_order_four` proves this complete statement.
Equivalently, the four-sample separation probability on the full probability
simplex is at most 183/1024, with equality exactly at the uniform board.

The source is the Lab's P0174 note `SIXTH_DEGREE_FOUR_BY_FOUR_K4.md` and its
exact coefficient data. This is the order-four component of the alternative
square proof described in [SOURCES](SOURCES.md); the broader priority and
attribution qualifications there apply here too.

## The identity that proves the bound

Flatten the sixteen cells into a vector p, and put S=sum(p). Let F(p) denote
the actual homogeneous quartic separation polynomial. Inclusion-exclusion
gives F(p)=24 times the sum of the row-product and column-product, minus
24 times the permanent. Thus the factor 24 and the intersection subtraction
come from the ordered iid event itself.

The degree-six gap has the exact identity

    (183/1024) S^6 - S^2 F(p)
      = sum over unordered four-cell multisets a of p^a (p^T Q_a p).

Each Q_a is a rational symmetric 16-by-16 matrix defined by the certificate
formulas. The outer sum contains each multiset once; it has no multinomial
factor. Every matrix satisfies

    p^T Q_a p >= (1/10) (sum_i p_i^2 - S^2/16).

The expression on the right is (1/10) times the sum of the squared centered
coordinates. The certificate is therefore nonnegative whenever all cells
are nonnegative. Setting S=1 proves the probability bound.

This also proves equality on every boundary face. At mass one, some cell
p_i is positive. The multiset consisting of that cell repeated four times
has positive weight p_i^4. If the whole certificate vanishes, its quadratic
form vanishes, forcing every centered coordinate to be zero. Hence all
sixteen cells are 1/16. No positive-entry hypothesis or limit argument is
needed.

## Why the finite checks cover every polynomial coefficient

There are 3,876 unordered quartic cell multisets. Actual permutations of
the four rows and four columns
reduce their matrices to 33 checked seeds. All physical witnesses are
checked in Lean. For the seeds, the 8,448 entries, 33 Gram identities and
495 positive pivots establish the quantitative bound and constant kernel.

Both sextic polynomials are homogeneous and invariant under the same
physical renamings. Their coefficients reduce to 224 representatives.
Coverage is proved by removing two cells from an arbitrary sextic multiset,
applying the already proved quartic reduction, and checking the two remaining
cells. This gives 33*16^2=8,448 checked augmented-seed witnesses; composition
of their actual permutations supplies the full coverage theorem.

The two sides of the identity are checked through separately proved
coefficient formulas. The actual gap uses the ordered sampling quartic;
the certificate uses deletion of its two quadratic cells. All 224 gap
coefficients and all 224 certificate coefficients agree exactly. Polynomial
extensionality then proves the identity above. A list of orbit counts alone
would not establish this identity; the physical coverage and coefficient
extraction lemmas are part of the formal proof.

## Source map and replay

- `Square/OrderFourPolynomial` ties the polynomial to the actual event.
- `Certificates/SpectralFour` and `Square/OrderFourOrbitPSD` establish all
  multiplier matrix bounds.
- `Square/OrderFourPolynomialCertificate` and `OrderFourPolynomialBound`
  prove evaluation, nonnegativity and boundary rigidity.
- `Square/OrderFourOrbitSextic` and `OrderFourOrbitAugmentedCoverage` prove
  complete sextic coverage by physical permutations.
- `Square/OrderFourPolynomialGapCheck`, `OrderFourPolynomialSexticCheck`
  and `OrderFourPolynomialIdentity` prove the actual sextic identity.
- `Square/OrderFourFinal` gives both normalized theorems and exact equality.

Run `lake build Test.OrderFour`. The test expands the original matrix
formula, checks the exact probability value, rejects a smaller constant,
and proves strictness when a probability board has a zero cell. Its five
final axiom audits allow only `propext`, `Classical.choice`, and `Quot.sound`.

The optional `python3 scripts/generate_order_four_orbits.py` reproduces the
finite data using exact arithmetic. It supplies no proof authority: all
finite gates use ordinary Lean kernel reduction. The implementing agent's
complete replay and another agent's semantic review both passed. The full
project still requires its combined build and independent release gate.
