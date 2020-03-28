------------------------------- MODULE Paxos -------------------------------

(***************************************************************************)
(* a specification of paxos which follows the description from             *)
(* - Lamport, Leslie. "Paxos made simple." ACM Sigact News 32.4 (2001)     *)
(* - wikipedia: https://en.wikipedia.org/wiki/Paxos_(computer_science)     *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

----------------------------------------------------------------------------

(***************************************************************************)
(* P: set of proposers                                                     *)
(* A: set of acceptors                                                     *)
(* L: set of learners                                                      *)
(***************************************************************************)

CONSTANT P, A, L
ASSUME IsFiniteSet(P) /\ IsFiniteSet(A) /\ IsFiniteSet(L)

(***************************************************************************)
(* N: set of valid numbers created by proposer                             *)
(*    which uniquely identifies the PREPARE message                        *)
(***************************************************************************)

CONSTANT N
ASSUME N \subseteq Nat

(***************************************************************************)
(* V: set of values to be chosen                                           *)
(***************************************************************************)

CONSTANT V

----------------------------------------------------------------------------

(***************************************************************************)
(* I: inboxes of all replicas                                              *)
(* O: outboxes of all replicas                                             *)
(***************************************************************************)

VARIABLE I, O

----------------------------------------------------------------------------

(***************************************************************************)
(* R: all the replicas (proposers, accpetors and learners)                 *)
(***************************************************************************)

R == UNION {P, A, L}

(***************************************************************************)
(* Send: send message m from x to y                                        *)
(*     m: message                                                          *)
(*     x: sender                                                           *)
(*     y: set of recivers                                                  *)
(*                                                                         *)
(* actually message lost is ignored here, but if you want to introduce it  *)
(* into the specification, just add '\E recieved \in y:' and replace 'y'   *)
(* to 'recieved' in the orginal expression                                 *)
(***************************************************************************)

Send(x, y, m) ==
  /\ I' = [v \in R |-> I[v] \union IF v \in y THEN {m} ELSE {}]
  /\ O' = [O EXCEPT ![x] = @ \union {m}]

----------------------------------------------------------------------------

(***************************************************************************)
(* Phase1A:                                                                *)
(*                                                                         *)
(* A proposer selects a proposal number n and sends a prepare request with *)
(* number n to a majority of acceptors                                     *)
(***************************************************************************)

Phase1A ==
  \E n \in N, p \in P, as \in SUBSET A:
    /\ Cardinality(as) * 2 > Cardinality(A)
    /\ Cardinality({o \in O[p]: o["t"] = "PREPARE" /\ o["n"] >= n}) = 0
    /\ Send(p, as, [t |-> "PREPARE", n |-> n, s |-> p])

(***************************************************************************)
(* Phase1B:                                                                *)
(*                                                                         *)
(* If an acceptor receives a prepare request with number n greater than    *)
(* that of any prepare request to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* numbered less than n and with the highest-numbered proposal (if any)    *)
(* that it has accepted.                                                   *)
(***************************************************************************)

Phase1B ==
  \E a \in A: \E i \in I[a]:
    /\ i["t"] = "PREPARE"
    /\ Cardinality({o \in O[a]: o["t"] = "PROMISE" /\ o["n"] >= i["n"]}) = 0
    /\ IF Cardinality({o \in O[a]: o["t"] = "ACCEPTED"}) = 0
       THEN Send(a, {i["s"]}, [t |-> "PROMISE", n |-> i["n"], s |-> a, m |-> 0, w |-> 0])
       ELSE \E x \in {o \in O[a]: o["t"] = "ACCEPTED"}:
              Send(a, {i["s"]}, [t |-> "PROMISE", n |-> i["n"], s |-> a, m |-> x["m"], w |-> x["w"]])

(***************************************************************************)
(* Phase2A:                                                                *)
(*                                                                         *)
(* If the proposer receives a response to its prepare requests (numbered n)*)
(* from a majority of acceptors, then it sends an accept request to each   *)
(* of those acceptors for a proposal numbered n with a value v, where v is *)
(* the value of the highest-numbered proposal among the responses, or is   *)
(* any value if the responses reported no proposals.                       *)
(***************************************************************************)

Phase2A ==
  \E n \in N, p \in P, as \in SUBSET A: \E m \in I[p]:
    /\ Cardinality(as) * 2 > Cardinality(A)
    /\ \A a \in as: Cardinality({i \in I[p]: i["t"] = "PROMISE" /\ i["n"] = n /\ i["s"] = a}) > 0
    /\ m["t"] = "PROMISE"
    /\ m["n"] = n
    /\ m["s"] \in as
    /\ Cardinality({i \in I[p]: i["t"] = "PROMISE" /\ i["n"] = n /\ i["m"] > m["m"]}) = 0
    /\ Cardinality({o \in O[p]: o["t"] = "ACCEPT" /\ o["n"] >= n}) = 0
    /\ IF m["w"] = 0
       THEN \E v \in V: Send(p, as, [t |-> "ACCEPT", n |-> n, v |-> v, s |-> p])
       ELSE Send(p, as, [t |-> "ACCEPT", n |-> n, v |-> m["w"], s |-> p])

(***************************************************************************)
(* Phase2B:                                                                *)
(*                                                                         *)
(* If an acceptor receives an accept request for a proposal numbered n, it *)
(* accepts the proposal unless it has already responded to a prepare       *)
(* request having a number greater than n.                                 *)
(***************************************************************************)

Phase2B ==
  \E a \in A: \E i \in I[a]:
    /\ i["t"] = "ACCEPT"
    /\ Cardinality({o \in O[a] : o["t"] = "PROMISE" /\ o["n"] > i["n"]}) = 0
    /\ Cardinality({o \in O[a] : o["t"] = "ACCEPTED" /\ o["m"] >= i["n"]}) = 0
    /\ Send(a, UNION {L, P}, [t |-> "ACCEPTED", m |-> i["n"], w |-> i["v"], s |-> a])

(***************************************************************************)
(* Learned:                                                                *)
(*                                                                         *)
(* To learn that a value has been chosen, a learner must find out that a   *)
(* proposal has been accepted by a majority of acceptors                   *)
(***************************************************************************)

Learned ==
  \E n \in N, l \in L, v \in V, as \in SUBSET A:
    /\ Cardinality(as) * 2 > Cardinality(A)
    /\ \A a \in as: Cardinality({i \in I[l]: i["t"] = "ACCEPTED" /\ i["m"] = n /\ i["w"] = v /\ i["s"] = a}) > 0
    /\ Send(l, {l}, [t |-> "LEARNED", v |-> v])

----------------------------------------------------------------------------

(***************************************************************************)
(* all the inboxes and outboxes are empty when start                       *)
(***************************************************************************)

Init ==
  /\ I = [v \in R |-> {}]
  /\ O = [v \in R |-> {}]

(***************************************************************************)
(* the transition funtions can be one of the followings:                   *)
(*     phase 1a                                                            *)
(*     phase 1b                                                            *)
(*     phase 2a                                                            *)
(*     phase 2a                                                            *)
(*     value learned                                                       *)
(***************************************************************************)

Next ==
  \/ Phase1A
  \/ Phase1B
  \/ Phase2A
  \/ Phase2B
  \/ Learned

----------------------------------------------------------------------------

Spec == Init /\ [][Next]_<<I,O>>

LivenessSpec == Spec /\ WF_<<I,O>>(Next)

----------------------------------------------------------------------------

(***************************************************************************)
(* safety: no two distinct learners can learn different values             *)
(***************************************************************************)

ConditionSafety == [](Cardinality(UNION {{i \in I[l] : i["t"] = "LEARNED"} : l \in L}) < 2)

(***************************************************************************)
(* liveness: value will be eventually learned                              *)
(***************************************************************************)

ConditionLiveness == <>(\E l \in L: \E i \in I[l]: i["t"] = "LEARNED")

THEOREM Spec => ConditionSafety
=============================================================================
\* Modification History
\* Last modified Sat Mar 28 10:10:46 IST 2020 by user
\* Created Sat Feb 29 02:01:59 IST 2020 by user
