--------------- MODULE LearnerGraphs ----------------

EXTENDS LearnerGraph

CONSTANTS
    \* acceptors:
    a1,a2,a3,
    \* learners:
    la,lb,lc,
    \* values:
    v1,v2

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

Members(p) == {p[1],p[2]}
LG4 == [
    acceptors |-> {a1,a2,a3},
    learners |-> {la,lb,lc},
    quorums |-> [l \in {la,lb,lc} |->
        CASE l = lc -> {{a3,a1}}
        [] l = la -> {{a1,a2}}
        [] l = lb -> {{a2,a3}}
    ],
    safeSets |-> [e \in {la,lb,lc}\times {la,lb,lc} |->
        CASE Members(e) = {la,lb} -> {{a2,a3}} \* why not just a2? Because then the learner graph is not condensed
        [] Members(e) = {la,lc} -> {{a1}}
        [] Members(e) = {lb,lc} -> {{a1,a2,a3}} \* lb prefers la if la and lc disagree (if la and lc disagree it's because a1 is malicious)
        [] OTHER -> {{}}
    ]
]
ASSUME IsValidLearnerGraph(LG4)
ASSUME Condensed(LG4)

====================================================