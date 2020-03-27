------------------------------- MODULE Paxos -------------------------------

(***************************************************************************)
(* a specification of paxos which follows the description from wikipedia   *)
(* https://en.wikipedia.org/wiki/Paxos_(computer_science)                  *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

----------------------------------------------------------------------------

(***************************************************************************)
(* P: set of proposers                                                     *)
(* A: set of acceptors                                                     *)
(* L: set of learners                                                      *)
(***************************************************************************)

CONSTANT P, A, L

(***************************************************************************)
(* N: set of valid numbers created by proposer                             *)
(*    which uniquely identifies the PREPARE message                        *)
(***************************************************************************)

CONSTANT N

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
(***************************************************************************)

Send(x, y, m) ==
  /\ I' = [v \in R |-> I[v] \union IF v \in y THEN {m} ELSE {}]
  /\ O' = [O EXCEPT ![x] = @ \union {m}]

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
  \/ \E n \in N, p \in P, as \in SUBSET A:
       /\ Cardinality(as) * 2 > Cardinality(A)
       /\ Cardinality({o \in O[p]: o["t"] = "PREPARE" /\ o["n"] >= n}) = 0
       /\ Send(p, as, [t |-> "PREPARE", n |-> n, s |-> p])
  \/ \E a \in A: \E i \in I[a]:
       /\ i["t"] = "PREPARE"
       /\ Cardinality({o \in O[a]: o["t"] = "PROMISE" /\ o["n"] >= i["n"]}) = 0
       /\ IF Cardinality({o \in O[a]: o["t"] = "ACCEPTED"}) = 0
          THEN Send(a, {i["s"]}, [t |-> "PROMISE", n |-> i["n"], s |-> a, m |-> 0, w |-> 0])
          ELSE \E x \in {o \in O[a]: o["t"] = "ACCEPTED"}:
                 Send(a, {i["s"]}, [t |-> "PROMISE", n |-> i["n"], s |-> a, m |-> x["m"], w |-> x["w"]])
  \/ \E n \in N, p \in P, as \in SUBSET A: \E m \in I[p]:
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
  \/ \E a \in A: \E i \in I[a]:
       /\ i["t"] = "ACCEPT"
       /\ Cardinality({o \in O[a] : o["t"] = "PROMISE" /\ o["n"] > i["n"]}) = 0
       /\ Cardinality({o \in O[a] : o["t"] = "ACCEPTED" /\ o["m"] >= i["n"]}) = 0
       /\ Send(a, UNION {L, P}, [t |-> "ACCEPTED", m |-> i["n"], w |-> i["v"], s |-> a])
  \/ \E n \in N, l \in L, v \in V, as \in SUBSET A:
       /\ Cardinality(as) * 2 > Cardinality(A)
       /\ \A a \in as: Cardinality({i \in I[l]: i["t"] = "ACCEPTED" /\ i["m"] = n /\ i["w"] = v /\ i["s"] = a}) > 0
       /\ Send(l, {l}, [t |-> "LEARNED", v |-> v])
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

THEOREM Spec => []ConditionSafety
=============================================================================
\* Modification History
\* Last modified Fri Mar 27 09:19:06 SGT 2020 by user
\* Created Thu Feb 17 18:00:54 SGT 2020 by user
