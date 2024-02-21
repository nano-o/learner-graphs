------ MODULE TLCReliableBroadcast ---------

EXTENDS ReliableBroadcast

CONSTANTS
    \* acceptors:
    a1,a2,a3,a4,a5,a6,
    \* learners:
    la,lb,lc,
    \* values:
    v1,v2

V1 == {v1,v2}
B1 == {}
W1 == {a2,a3}
B2 == {a1}
LG1 == [
    acceptors |-> {a1,a2,a3},
    learners |-> {la,lb},
    quorums |-> [l \in {la,lb} |-> {{a1,a2},{a1,a3},{a2,a3}}],
    safeSets |-> [e \in {la,lb}\times {la,lb} |-> {{a1,a2,a3}}]
]
ASSUME IsValidLearnerGraph(LG1)
LG2 == [
    acceptors |-> {a1,a2,a3},
    learners |-> {la,lb},
    quorums |-> [l \in {la,lb} |->
        IF l = la 
        THEN {{a1,a2}}
        ELSE {{a1,a3}}],
    safeSets |-> [e \in {la,lb}\times {la,lb} |-> {{a1,a2,a3}}]
]
ASSUME IsValidLearnerGraph(LG2)

\* Isaac's example:
B3 == {a1}
W3 == {a2,a3,a4,a5,a6}
Members(p) == {p[1],p[2]}
LG3 == [
    acceptors |-> {a1,a2,a3,a4,a5,a6},
    learners |-> {la,lb,lc},
    quorums |-> [l \in {la,lb,lc} |->
        CASE l = lc -> {{a5,a6,a1}}
        [] l = la -> {{a1,a2,a3}}
        [] l = lb -> {{a3,a4,a5}}
    ],
    safeSets |-> [e \in {la,lb,lc}\times {la,lb,lc} |->
        CASE Members(e) = {la,lb} -> {{a3}}
        [] Members(e) = {la,lc} -> {{a1}}
        [] Members(e) = {lb,lc} -> {{a1,a5}} \* lb prefers la if la and lc disagree
        [] OTHER -> {{}}
    ]
]
ASSUME IsValidLearnerGraph(LG3)
\* Simplified:
B4 == {a1}
W4 == {a2,a3}
LG4 == [
    acceptors |-> {a1,a2,a3},
    learners |-> {la,lb,lc},
    quorums |-> [l \in {la,lb,lc} |->
        CASE l = lc -> {{a3,a1}}
        [] l = la -> {{a1,a2}}
        [] l = lb -> {{a2,a3}}
    ],
    safeSets |-> [e \in {la,lb,lc}\times {la,lb,lc} |->
        CASE Members(e) = {la,lb} -> {{a2}}
        [] Members(e) = {la,lc} -> {{a1}}
        [] Members(e) = {lb,lc} -> {{a1,a3}} \* lb prefers la if la and lc disagree
        [] OTHER -> {{}}
    ]
]
ASSUME IsValidLearnerGraph(LG4)

Canary1 == \neg (
    \E l \in LG.learners : pc[l] = "Done"
)
Canary2 == \neg (
    pc[la] = "Done" /\ pc[lb] = "Done" /\ output[la] # output[lb]
)
Canary3 == \neg (
    \E val1,val2 \in V : \E acc1,acc2 \in Acceptor : \E l1,l2 \in Learner :
        /\  val1 # val2
        /\  val1 \in ready[acc1][l1]
        /\  val2 \in ready[acc2][l2]
)
============================================