--------------- MODULE LearnerGraph ----------------

(****************************************************************************)
(* A learner graph is a record with four fields:                            *)
(*                                                                          *)
(*     - learners: a set of learners                                        *)
(*     - acceptors: a set of acceptors                                      *)
(*     - quorums: a function mapping a learner to its minimal quorums       *)
(*     - safeSets: a function mapping a pair of learners l1 and l2 to their *)
(*       minimal safe sets.                                                 *)
(****************************************************************************)

Reverse(p) == <<p[2], p[1]>>
X \subset Y == X # Y /\ X \subseteq Y

IsLearnerGraph(lg) ==
    \* NOTE quorums and safe sets should be minimal
    /\  lg.quorums \in [lg.learners -> SUBSET SUBSET lg.acceptors]
    /\  \A l \in lg.learners : \A Q1 \in lg.quorums[l] : \neg (\exists Q2 \in lg.quorums[l] : Q2 \subset Q1)
    /\  lg.safeSets \in [lg.learners \times lg.learners -> SUBSET SUBSET lg.acceptors]
    /\  \A p \in lg.learners\times lg.learners : 
            /\  lg.safeSets[p] = lg.safeSets[Reverse(p)]
            /\  \A s1 \in lg.safeSets[p] : \neg (\exists s2 \in lg.safeSets[p] : s2 \subset s1)

IsValidLearnerGraph(lg) ==
    /\  IsLearnerGraph(lg)
    /\  \A l1,l2 \in lg.learners : l1 # l2 =>
            \A s \in lg.safeSets[<<l1,l2>>] :
                \A q1 \in lg.quorums[l1] : 
                    \A q2 \in lg.quorums[l2] :
                        s \cap q1 \cap q2 # {}

Condensed(lg) == \A l1,l2,l3 \in lg.learners :
    l1 # l2 /\ l2 # l3 /\ l1 # l3 =>
        \A s1 \in lg.safeSets[<<l1,l2>>] :
            \A s2 \in lg.safeSets[<<l2,l3>>] :
                \E s3 \in lg.safeSets[<<l1,l3>>] : s3 \subseteq s1 \cup s2

====================================================