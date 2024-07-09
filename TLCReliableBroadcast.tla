------ MODULE TLCReliableBroadcast ---------

EXTENDS ReliableBroadcast, LearnerGraphs

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