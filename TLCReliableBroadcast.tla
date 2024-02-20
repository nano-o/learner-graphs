------ MODULE TLCReliableBroadcast ---------

CONSTANTS
    a1,a2,a3,
    l1,l2,
    v1,v2

V == {v1,v2}
B == {}
W == {a2,a3}

LG == [
    acceptors |-> {a1,a2,a3},
    learners |-> {l1,l2},
    quorums |-> [l \in {l1,l2} |-> {{a1,a2},{a1,a3},{a2,a3}}],
    safeSets |-> [e \in {l1,l2}\times {l1,l2} |-> {{a1,a2,a3}}]
]

VARIABLES bcast, echo, ready, pc, output

INSTANCE ReliableBroadcast

ASSUME IsValidLearnerGraph(LG)

Canary1 == \neg (
    \E l \in LG.learners : pc[l] = "Done"
)

============================================