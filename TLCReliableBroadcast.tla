------ MODULE TLCReliableBroadcast ---------

EXTENDS ReliableBroadcast

CONSTANTS
    a1,a2,a3,
    l1,l2,
    v1,v2

V1 == {v1,v2}
B1 == {}
W1 == {a2,a3}
B2 == {a1}
LG1 == [
    acceptors |-> {a1,a2,a3},
    learners |-> {l1,l2},
    quorums |-> [l \in {l1,l2} |-> {{a1,a2},{a1,a3},{a2,a3}}],
    safeSets |-> [e \in {l1,l2}\times {l1,l2} |-> {{a1,a2,a3}}]
]
ASSUME IsValidLearnerGraph(LG1)
LG2 == [
    acceptors |-> {a1,a2,a3},
    learners |-> {l1,l2},
    quorums |-> [l \in {l1,l2} |->
        IF l = l1 
        THEN {{a1,a2}}
        ELSE {{a1,a3}}],
    safeSets |-> [e \in {l1,l2}\times {l1,l2} |-> {{a1,a2,a3}}]
]
ASSUME IsValidLearnerGraph(LG2)

Canary1 == \neg (
    \E l \in LG.learners : pc[l] = "Done"
)
Canary2 == \neg (
    pc[l1] = "Done" /\ pc[l2] = "Done" /\ output[l1] # output[l2]
)
============================================