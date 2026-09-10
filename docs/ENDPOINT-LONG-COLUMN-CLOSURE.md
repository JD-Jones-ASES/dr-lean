# Long-column kernel and probability closure

[LongColumnKernel](../DR/Endpoint/LongColumnKernel.lean) proves positivity
of the actual averaging kernel of a nonnegative retained board. Its inputs
are `m≥16`, `N≥10000m²`, retained mass greater than `3/4`, scaled row
square deviation below `1/9`, and column masses at most `25/N`.
The retained board is not assumed to have total mass one.

The proof derives positive retained rows and bounds the collision
intensity of their normalized row law by 1/12. The union bound then gives
avoidance at least 11/12. The elementary coefficient lower bound and
factorial estimate imply the collision-cluster kernel criterion, with
a strict margin in the stated dimensions.

[LongColumnDeletion](../DR/Endpoint/LongColumnDeletion.lean) uses the
asymmetric square weights `5/4` and `5` to retain the original scaled row
budget `1/16` after deletion of mass at most `1/(100m)`.
[LongColumnClosure](../DR/Endpoint/LongColumnClosure.lean) derives those
deletion conditions from the actual original column cap. Its final
`uniform_maximum_endpoint_of_longColumn_caps` consumes these two bounds
for every actual contender and proves the full sharp endpoint inequality
with iff uniform equality. The [concentration theorem](ENDPOINT-LONG-COLUMN-CONCENTRATION.md)
proves the needed column cap and row estimates from the leading gauge.
The [quadratic](ENDPOINT-QUADRATIC.md) and [quartic](ENDPOINT-QUARTIC.md)
dimension bounds reduce those estimates to the two caps used here.

## Formal statements

[LongColumnKernel](../DR/Endpoint/LongColumnKernel.lean), [LongColumnDeletion](../DR/Endpoint/LongColumnDeletion.lean), [LongColumnClosure](../DR/Endpoint/LongColumnClosure.lean).
