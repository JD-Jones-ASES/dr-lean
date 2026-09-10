# Long-column kernel and probability closure

[LongColumnKernel](../DR/Endpoint/LongColumnKernel.lean) proves positivity
of the actual averaging kernel of a nonnegative retained board. Its inputs
are `m≥16`, `N≥10000m²`, retained mass greater than `3/4`, scaled row
square deviation below `1/9`, and column masses at most `25/N`.
The retained board is not assumed to have total mass one.

The proof derives positive retained rows, bounds the collision intensity
of their own normalized row law by `1/12`, and obtains actual avoidance
at least `11/12`. The existing exact elementary-coefficient guard then
supplies the collision-cluster kernel criterion. This reuses a slightly
coarser coefficient estimate than the Lab's sharper collision-union formula;
the admitted dimensions give ample strict margin.

[LongColumnDeletion](../DR/Endpoint/LongColumnDeletion.lean) uses the
asymmetric square weights `5/4` and `5` to retain the original scaled row
budget `1/16` after deletion of mass at most `1/(100m)`.
[LongColumnClosure](../DR/Endpoint/LongColumnClosure.lean) derives those
deletion conditions from the actual original column cap. Its final
`uniform_maximum_endpoint_of_longColumn_caps` consumes these two bounds
for every actual contender and proves the full sharp endpoint inequality
with iff uniform equality. The upstream concentration theorem is still
a separate proof obligation; this foundation alone closes no new range.

`lake --wfail build Test.LongColumnClosure` passed 3,305 jobs, seven
examples and six standard-only axiom audits. Tests include a literal
nonuniform deletion, zero deletion, rejected signed deletion, the necessity
of the improved square estimate, an actual retained board of mass `7/8`,
uniform inputs with two actual zero columns after deletion, and rejection
of the row-deviation premise for a zero original row.
