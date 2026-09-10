# Actual transition column deletion

Deleting any two distinct columns of an endpoint contender preserves
the row and column estimates needed for the localized kernel criterion
throughout the range

```
10^18<=m, m<=n, m*(m-1)<=20*n, n<=10000*m^2.
```

The original contender row budget is `<1/100`, not the
earlier LLL strip's stronger `<1/1024` budget. The exact centered deletion
vector and squared triangle estimate give retained normalized squared row
deviation `<1/9` when `m*w<=1/16`. Unequal deletion masses and zero deleted
coordinates are retained. Consequently every retained normalized row is
strictly greater than `2/(3m)`.

The integer transition lower edge and `m>=10^18` imply `4096*m^3<=n^2`
by exact arithmetic. The original column cap is `<2/n`, and deletion leaves
mass `h>15/16`. The retained board's own normalized row law has column cap
`4m/n`, with `m*(4m/n)^2<=1/256`; its sequential elementary coefficient
cap holds as well. No bound for original-row avoidance is substituted for
retained-row avoidance.

## Formal statements

[TransitionDeletionBalance](../DR/Endpoint/TransitionDeletionBalance.lean), [TransitionDeletion](../DR/Endpoint/TransitionDeletion.lean).
