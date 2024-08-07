------ MODULE ReliableBroadcastFD ------

EXTENDS LearnerGraph, FiniteSets

CONSTANTS
    LG, \* the learner graph
    B, \* the set of malicious acceptors
    W, \* the set of well-behaved acceptors, i.e. honest and available
    V \* the set of values that can be broadcast

ASSUME B \cap W = {}

ASSUME IsValidLearnerGraph(LG)
ASSUME Condensed(LG)

Learner == LG.learners
Acceptor == LG.acceptors

HonestAcceptor == Acceptor \ B
\* Note that HonestAcceptor is not necessary equal to W

(*--algorithm ReliableBroadcast {

    \* Global variables:
    variables
        bcast \in (SUBSET V) \ {{}}; \* the `^value(s)^' broadcast; multiple values model a malicious sender
        echo = [a \in Acceptor |-> {}]; \* echo messages sent by the acceptors
        \* ready messages sent by the acceptors; note that acceptors get ready per learner:
        ready = [a \in Acceptor |-> [l \in Learner |-> {}]];
        fd = [a \in Acceptor |-> {}]; \* failure-detector output

    define {
        KnowsNotEntangled(self,l1,l2) ==
            \* acceptor `self` knows that learners `l1` and `l2` are not entangled when both:
            /\  l1 # l2 \* a learner is always entangled with itself
            \* l1 and l2 don't have to agree if none of their safe sets are completely well-behaved:
            /\  \A S \in LG.safeSets[<<l1,l2>>] :
                    \E a \in S : a \in fd[self]
    }
    (*******************************************************************************)
    (* Each process get outputs from a failure-detector that eventually identifies *)
    (* all malicious processes (we enforce this eventuality by making the          *)
    (* failure-detector process below a fair process):                             *)
    (*******************************************************************************)
    fair process (fd \in {"failure-detector"})
    {
l0:     while (\E a \in HonestAcceptor : \E b \in B : b \notin fd[a])
        with (a \in HonestAcceptor, b \in B) { \* NOTE notation idea: while some () {}
            when b \notin fd[a];
            fd[a] := fd[a] \cup {b};
        }
    }
    fair process (learner \in Learner)
        variables
            output = <<>>;
    {
        \* a learner outputs when one of its quorums is ready:
l0:     with (v \in V) {
            when \E Q \in LG.quorums[self] :
                \A a \in Q : v \in ready[a][self];
            output := v;
        }
    }
    process (acceptor \in Acceptor) {
l0:     while (TRUE)
        either \* echo a unique value (unless malicious)
            with (v \in V) {
                when v \in bcast;
                when self \notin B => echo[self] = {}; \* malicious nodes can echo different values
                echo[self] := echo[self] \cup {v};
            }
        or \* send ready when witnessing a quorum of echoes
            with (v \in V)
            with (l \in Learner)
            with (Q \in LG.quorums[l]) {
                when ready[self][l] = {};
                when \A a \in Q : v \in echo[a];
                \* check for conflicts (NOTE needed for safety):
                when \A l2 \in Learner : \A v2 \in V \ {v} :
                    v2 \in ready[self][l2] => KnowsNotEntangled(self,l,l2);
                ready[self][l] := ready[self][l] \cup {v};
            }
        or \* send ready when blocked by ready acceptors
            with (v \in V)
            with (l1 \in Learner, l2 \in Learner) {
                when v \in bcast;
                when ready[self][l1] = {}; \* no good... but no good without it either (liveness fails in both cases)
                when \A Q \in LG.quorums[l1] :
                    \E a2 \in Q : v \in ready[a2][l2];
                \* check for conflicts:
                when \A l3 \in Learner \ {l1} : \A v2 \in V \ {v} :
                    v2 \in ready[self][l3] => KnowsNotEntangled(self,l1,l3);
                ready[self][l1] := ready[self][l1] \cup {v};
            }
        }
}*)

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
