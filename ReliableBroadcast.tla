------ MODULE ReliableBroadcast ------

EXTENDS LearnerGraph, FiniteSets

CONSTANTS
    LG, \* the learner graph
    B, \* the set of malicious acceptors
    W, \* the set of well-behaved acceptors, i.e. honest and available
    V \* the set of values that can be broadcast

ASSUME B \cap W = {}

ASSUME IsValidLearnerGraph(LG)

Learner == LG.learners
Acceptor == LG.acceptors

HonestAcceptor == Acceptor \ B
\* Note that HonestAcceptor is not necessary equal to W


(*--algorithm ReliableBroadcast {
    variables
        bcast \in (SUBSET V) \ {{}}; \* the `^value(s)^' broadcast; multiple values model a malicious sender
        echo = [a \in Acceptor |-> {}];
        ready = [a \in Acceptor |-> [l \in Learner |-> {}]];
    define {
        ProvenMalicious(a) == \E v1,v2 \in V :
            /\  v1 # v2
            /\  \/  {v1,v2} \subseteq echo[a]
                \* TODO: this is recursive:
                \* \/  \E l1,l2 \in Learner :
                \*     /\  l1 # l2
                \*     /\  v1 \in ready[a][l1]
                \*     /\  v2 \in ready[a][l2]
                \*     /\  \neg NotEntangled(l1,l2)
        NotEntangled(l1,l2) == 
            /\  l1 # l2 \* a learner is always entangled with itself
            /\  \A S \in LG.safeSets[<<l1,l2>>] :
                    \E a \in S : ProvenMalicious(a)
    }
    fair process (learner \in Learner)
        variables
            output = <<>>;
    {
l0:     with (v \in V) {
            when \E Q \in LG.quorums[self] :
                \A a \in Q : v \in ready[a][self];
            output := v;
        }
    }
    \* `^\newpage^'
    process (acceptor \in HonestAcceptor) {
l0:     while (TRUE)
        either
            with (v \in V) {
                when v \in bcast /\ echo[self] = {};
                echo[self] := echo[self] \cup {v};
            }
        or
            with (v \in V)
            with (l \in Learner)
            with (Q \in LG.quorums[l]) {
                when ready[self][l] = {};
                when \A a \in Q : v \in echo[a];
                \* check for conflicts:
                when \A l2 \in Learner : \A v2 \in V \ {v} :
                    v2 \in ready[self][l2] => NotEntangled(l,l2);
                ready[self][l] := ready[self][l] \cup {v};
            }
        or
            with (v \in V)
            with (l1 \in Learner, l2 \in Learner) {
                when \A Q \in LG.quorums[l1] : \E a2 \in Q : 
                    /\  v \in ready[a2][l2]
                    /\  v \in bcast;
                    \* and we need a proof for the ready message:
                    \* /\  \E Q2 \in LG.quorums[l2] : \A a3 \in Q2 : v \in echo[a3];
                \* check for conflicts:
                when \A l3 \in Learner \ {l1} : \A v2 \in V \ {v} :
                    v2 \in ready[self][l3] => NotEntangled(l1,l3);
                ready[self][l1] := ready[self][l1] \cup {v};
            }
        }
    process (byzAcceptor \in B) {
l0:     while (TRUE) {
            either
            with (v \in V)
                echo[self] := echo[self] \cup {v}
            or
            with (l \in Learner) {
                with (v \in V)
                    ready[self][l] := ready[self][l] \cup {v};
            }
        }
    }
}
*)

\* `^\newpage^'

TypeOK ==
    /\  bcast \in (SUBSET V) \ {{}}
    /\  echo \in [Acceptor -> (SUBSET V)]
    /\  ready \in [Acceptor -> [Learner -> (SUBSET V)]]
    /\  output \in [Learner -> V \cup {<<>>}]

\* Two learners must agree if one of their safe sets is fully well-behaved:
Entangled(l1, l2) == \E S \in LG.safeSets[<<l1,l2>>] :
    S \cap B = {}

LiveLearner == {l \in Learner : 
    \E Q \in LG.quorums[l] : Q \subseteq W}

Safety ==
    /\  \A l \in Learner :
        /\  pc[l] = "Done"
        /\  \E Q \in LG.quorums[l] : Q \cap B = {} \* SafeLearner
        =>  output[l] \in bcast
    /\  \A l1,l2 \in Learner :
        /\  Entangled(l1,l2)
        /\  pc[l1] = "Done"
        /\  pc[l2] = "Done"
        =>  output[l1] = output[l2]

Liveness ==
    /\  Cardinality(bcast) = 1 =>
            \A l \in LiveLearner : <>(pc[l] = "Done" /\ bcast = {output[l]})
    \* This one is interesting (I think this is the best we can guarantee):
    /\  \A l1 \in Learner : \A l2 \in LiveLearner : Entangled(l1,l2) =>
            [](pc[l1] = "Done" => <>(pc[l2] = "Done"))

FairSpec ==
    /\  Spec
    /\  \A a \in W : WF_vars(acceptor(a))

================================        
