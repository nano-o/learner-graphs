------ MODULE TLCReliableBroadcastFD ---------

EXTENDS ReliableBroadcastFD, TLC

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

State1 == 
/\ fd = (a1 :> {} @@ a2 :> {a1} @@ a3 :> {a1})
/\ bcast = {v1, v2}
/\ pc = ( a1 :> "l0" @@
  a2 :> "l0_a" @@
  a3 :> "l0_a" @@
  la :> "Done" @@
  lb :> "l0_l" @@
  lc :> "l0_l" @@
  "failure-detector" :> "Done" )
/\ ready = ( 
  a1 :> (la :> {v2} @@ lb :> {} @@ lc :> {}) @@
  a2 :> (la :> {v1, v2} @@ lb :> {} @@ lc :> {v2}) @@
  a3 :> (la :> {v2} @@ lb :> {v2} @@ lc :> {v2}) )
/\ output = (la :> v2 @@ lb :> <<>> @@ lc :> <<>>)
/\ echo = (a1 :> {v1} @@ a2 :> {v1} @@ a3 :> {v2})

FairSpec2 ==
    /\ State1 /\ [][Next]_vars
    /\ \A self \in {"failure-detector"} : WF_vars(fd_(self))
    /\ \A self \in Learner : WF_vars(learner(self))
    /\ \A a \in W : WF_vars(acceptor(a))

============================================
