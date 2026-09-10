# Actual contender deletion estimates on the LLL strip

`LLLStripParameters.lean` and `LLLStripDeletion.lean` prove the retained
board estimates for the exact domain

```
m>=128, 4096*m^3<=n^2, 20*n<=m*(m-1).
```

The lower inequality is equivalent to `64*m^(3/2)<=n` on nonnegative
integer dimensions. It implies `n>=64m`, and the upper inequality implies
`n<=m^2`. The actual full-probability contender column cap becomes
strictly less than `2/n`; its row concentration comes from the actual
uniform avoidance bound.

For every pair of distinct columns, the retained board has total mass
strictly above `15/16`, positive row masses, and normalized row squared
deviation below `1/81`. Its own normalized independent-row law has column
cap `4m/n`, with `m*(4m/n)^2<=1/256`. The retained elementary coefficient's
sequential cap condition also holds. Neither the original row law nor its
collision avoidance probability is substituted for the retained law.

## Formal statements

[LLLStripParameters](../DR/Endpoint/LLLStripParameters.lean), [LLLStripDeletion](../DR/Endpoint/LLLStripDeletion.lean).
