--------------- MODULE LearnerGraph ----------------

(**********************************************************************************)
(* A learner graph is a record with four fields:                                  *)
(*                                                                                *)
(*     - learners: a set of learners                                              *)
(*     - acceptors: a set of acceptors                                            *)
(*     - quorums: a function from learners to sets of sets of acceptors           *)
(*     - safeSets: a function from pairs of learners to sets of sets of acceptors *)
(**********************************************************************************)

Reverse(p) == <<p[2], p[1]>>

IsLearnerGraph(lg) ==
    /\  lg.quorums \in [lg.learners -> SUBSET SUBSET lg.acceptors]
    /\  lg.safeSets \in [lg.learners \times lg.learners -> SUBSET SUBSET lg.acceptors]
    /\  \A p \in lg.learners\times lg.learners : lg.safeSets[p] = lg.safeSets[Reverse(p)]

IsValidLearnerGraph(lg) ==
    /\  IsLearnerGraph(lg)
    /\  \A l1,l2 \in lg.learners : l1 # l2 =>
            \A s \in lg.safeSets[<<l1,l2>>] :
                \A q1 \in lg.quorums[l1] : 
                    \A q2 \in lg.quorums[l2] :
                        s \cap q1 \cap q2 # {}
    

====================================================