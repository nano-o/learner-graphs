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
        bcast \in (SUBSET V) \ {{}}; \* the value(s) broadcast; multiple values model a malicious sender
        echo = [a \in Acceptor |-> {}];
        ready = [a \in Acceptor |-> [l \in Learner |-> {}]];
    define {
        ProvenMalicious(a) == \E v1,v2 \in V :
            /\  v1 # v2
            /\  \/  {v1,v2} \subseteq echo[a]
                \/  \E l \in Learner : {v1,v2} \subseteq ready[a][l]
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
                ready[self][l] := ready[self][l] \cup {v}; 
            }
        or
            with (v \in V)
            with (l \in Learner)
            with (readyForV = {a \in Acceptor : v \in ready[a][l]}) {
                when \A Q \in LG.quorums[l] :
                    \/  Q \cap readyForV # {}
                    \/  \A a \in Q : ProvenMalicious(a);
                ready[self][l] := ready[self][l] \cup {v}; 
            }
    }
    process (byzAcceptor \in B) {
l0:     while (TRUE) {
            with (v \in V)
                echo[self] := echo[self] \cup {v};
            with (rdy \in [Learner -> V]) {
                ready[self] := [l \in Learner |-> ready[self][l] \cup {rdy[l]}];
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e073e0ef" /\ chksum(tla) = "f0610e59")
\* Label l0 of process learner at line 37 col 14 changed to l0_
\* Label l0 of process acceptor at line 44 col 9 changed to l0_a
VARIABLES bcast, echo, ready, pc

(* define statement *)
ProvenMalicious(a) == \E v1,v2 \in V :
    /\  v1 # v2
    /\  \/  {v1,v2} \subseteq echo[a]
        \/  \E l \in Learner : {v1,v2} \subseteq ready[a][l]

VARIABLE output

vars == << bcast, echo, ready, pc, output >>

ProcSet == (Learner) \cup (HonestAcceptor) \cup (B)

Init == (* Global variables *)
        /\ bcast \in (SUBSET V) \ {{}}
        /\ echo = [a \in Acceptor |-> {}]
        /\ ready = [a \in Acceptor |-> [l \in Learner |-> {}]]
        (* Process learner *)
        /\ output = [self \in Learner |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in Learner -> "l0_"
                                        [] self \in HonestAcceptor -> "l0_a"
                                        [] self \in B -> "l0"]

l0_(self) == /\ pc[self] = "l0_"
             /\ \E v \in V:
                  /\  \E Q \in LG.quorums[self] :
                     \A a \in Q : v \in ready[a][self]
                  /\ output' = [output EXCEPT ![self] = v]
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << bcast, echo, ready >>

learner(self) == l0_(self)

l0_a(self) == /\ pc[self] = "l0_a"
              /\ \/ /\ \E v \in V:
                         /\ v \in bcast /\ echo[self] = {}
                         /\ echo' = [echo EXCEPT ![self] = echo[self] \cup {v}]
                    /\ ready' = ready
                 \/ /\ \E v \in V:
                         \E l \in Learner:
                           \E Q \in LG.quorums[l]:
                             /\ ready[self][l] = {}
                             /\ \A a \in Q : v \in echo[a]
                             /\ ready' = [ready EXCEPT ![self][l] = ready[self][l] \cup {v}]
                    /\ echo' = echo
                 \/ /\ \E v \in V:
                         \E l \in Learner:
                           LET readyForV == {a \in Acceptor : v \in ready[a][l]} IN
                             /\  \A Q \in LG.quorums[l] :
                                \/  Q \cap readyForV # {}
                                \/  \A a \in Q : ProvenMalicious(a)
                             /\ ready' = [ready EXCEPT ![self][l] = ready[self][l] \cup {v}]
                    /\ echo' = echo
              /\ pc' = [pc EXCEPT ![self] = "l0_a"]
              /\ UNCHANGED << bcast, output >>

acceptor(self) == l0_a(self)

l0(self) == /\ pc[self] = "l0"
            /\ \E v \in V:
                 echo' = [echo EXCEPT ![self] = echo[self] \cup {v}]
            /\ \E rdy \in [Learner -> V]:
                 ready' = [ready EXCEPT ![self] = [l \in Learner |-> ready[self][l] \cup {rdy[l]}]]
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << bcast, output >>

byzAcceptor(self) == l0(self)

Next == (\E self \in Learner: learner(self))
           \/ (\E self \in HonestAcceptor: acceptor(self))
           \/ (\E self \in B: byzAcceptor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Learner : WF_vars(learner(self))

\* END TRANSLATION 

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
        /\  \E Q \in LG.quorums[l] : Q \cap B = {}
        =>  \E l2 \in Learner : output[l] \in bcast
    /\  \A l1,l2 \in Learner :
        /\  Entangled(l1,l2)
        /\  pc[l1] = "Done"
        /\  pc[l2] = "Done"
        =>  output[l1] = output[l2]

Liveness ==
    /\  Cardinality(bcast) = 1 =>
            \A l \in LiveLearner : <>(pc[l] = "Done" /\ bcast = {output[l]})
    \* This one is interesting (I think this is the best we can guarantee):
    /\  \A l1,l2 \in LiveLearner : Entangled(l1,l2) =>
            [](pc[l1] = "Done" => <>(pc[l2] = "Done"))

FairSpec ==
    /\  Spec
    /\  \A a \in W : WF_vars(acceptor(a))

================================        
