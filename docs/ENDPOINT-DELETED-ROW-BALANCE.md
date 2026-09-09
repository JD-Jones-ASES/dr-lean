# Actual row balance after column deletion

`DR/Endpoint/DeletedRowBalance.lean` supplies the retained-row estimate
needed in Section 2 of the Lab's `ENDPOINT_LLL_STRIP.md`. It works with
arbitrary nonnegative deleted row masses, including zeros. Given original
scaled-row squared deviation below `1/1024` and total deleted mass `w`
with `m*w<=1/16`, the retained normalized squared deviation is below
`1/81`, hence below the kernel criterion's `1/9` threshold.

The proof keeps the exact centered deletion vector `m*tau-w`. Its squared
norm is at most `m^2*w^2`. The elementary squared triangle bound and
`1-w>=15/16` yield the estimate directly. This slightly weaker bound than
the source's norm `1/10` is sufficient for the same final strip; no domain
is changed. A coordinate consequence gives every retained normalized row
strictly more than `2/(3m)`.

The actual-board adapter uses `keepColumns P S`, proves the deleted mass
identity from total mass one, and invokes no preexisting positive row-law
assumption. Replay: `lake build Test.DeletedRowBalance`. Checks include
unequal deletion, zero deletion coordinates, and failure when either the
small-deletion or original-concentration hypothesis is dropped.
