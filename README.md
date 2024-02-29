# Using TLA to explore solving reliable broadcast in the learner-graph model

The algorithm currently specified in [`ReliableBroadcast.tla`](./ReliableBroadcast.tla) violates the liveness property specified in the same file.
TLC finds the following counter-example.

We have 3 learners `la`, `lb`, and `lc` and 3 acceptos `a1`, `a2`, and `a3`.
Only `a1` is malicious.
Each learner has a single quorums: `la` has quorum `Qa={a1,a2}`, `lb` has quorum `Qb={a2,a3}`, and `lc` has quorum `Qc={a3,a1}`.
Finally, the safe sets are set up as follows: `la-lb={a2}`, `la-lc={a1}`, and `lb-lc={a1,a3}`.
This means that if `a1` only is malicious, then `la` and `lc` can disagree, and `lb` can disagree with `lc` but must agree with `la`.
This is all specified as `LG4` in [`TLCReliableBroadcast.tla`](./TLCReliableBroadcast.tla).

Now we can get into the following situation:
```tla
/\ echo = (
  a1 :> {v2} @@
  a2 :> {v2} @@
  a3 :> {v1})
/\ ready = (
  a1 :> (la :> {v1} @@ lb :> {} @@ lc :> {}) @@
  a2 :> (la :> {v1, v2} @@ lb :> {} @@ lc :> {}) @@
  a3 :> (la :> {v1, v2} @@ lb :> {} @@ lc :> {}) )
/\ output = (
  la :> v1 @@ lb :> <<>> @@ lc :> <<>>)
```
Here `la` has an output, and so the liveness property requires `lb` to output (because it has a fully-well-behaved quorum `{a2,a3}`).
However, `a2` and `a3` cannot get ready for `v1` for `lb` because they are ready for `v2 # v1` for `la` and, with the current protocol, they do not detect that `a1` is malicious (which would allow them to get ready for `v1` for `lb`).

TLC can produce a full trace as follows.
On Linux, first translate the PlucCal code to TLA with `make pcal`, then run the TLC model-checker with `make tlc`.

In this example we could detect that `a1` is malicious because it got ready for `v1` for `la` but there is no quorum of echoes for `v1`.
In general, it seems that we would need to check that acceptors get ready legitimately, which means possibly following a long chain of acceptors that are recursively blocked until we arrive at a quorum of echoes.

## Failure-detector version

Instead of trying to detect failures, we could assume that acceptors have access to a failure-detector abstraction that eventually identifies all malicious acceptors.
This is what we do in [`ReliableBroadcastFD.tla`](./ReliableBroadcastFD.tla).
