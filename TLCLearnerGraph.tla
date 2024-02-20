------ MODULE TLCLearnerGraph --------

CONSTANTS
    l1,l2,a1

LG == [
    learners |-> {l1,l2},
    acceptors |-> {a1},
    quorums |-> [l \in {l1,l2} |-> {{a1}}],
    safeSets |-> [p \in {l1,l2}\X{l1,l2} |-> {{a1}}]
]

INSTANCE LearnerGraph

ASSUME IsLearnerGraph(LG)
ASSUME IsValidLearnerGraph(LG)

======================================