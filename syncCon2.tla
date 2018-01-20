------------------------------ MODULE syncCon2 ------------------------------
\* zheng kai  50247576
\* xinbo yu   50102922
\* Synchronized Consensus
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, FAILNUM
ASSUME N <= 5 /\ 0 <= FAILNUM /\ FAILNUM <= 4
Nodes == 1 .. N
counter == 0   \* record the FailNum

(*
--algorithm syncCon2 {
    variables FailNum = FAILNUM;           \* Initialization block
              up = [n \in Nodes |-> TRUE]; \* Nodes are up
              pt = [n \in Nodes |-> 0];    \* Nodes are at round 0
              t = [n \in Nodes |-> FALSE]; \* Nodes are not terminated
              d = [n \in Nodes |-> -1];    \* Nodes are not decided
              mb = [ n \in Nodes |-> {}];  \* Nodes have mailbox as emptyset
                          
    define {
        SetMin(S) == CHOOSE i \in S : \A j \in S : i <= j
    }
    
    macro MaybeFail() {
        if (FailNum > 0 /\ up[self])
        {
            either { up[self] := FALSE; FailNum := FailNum - 1; counter:= counter+1}   \* if fail, counter = counter +1
            or skip;
        }
    }
    
    fair process(n \in Nodes)
    variables v = 0, Q = {};
    {
        P: if (up[self]) {
               v := self;
               Q := Nodes;
           PS: while (pt[self] <= counter) {
                   if (pt[self] = 0) {
                       Q := Nodes;
                       L1: while (up[self] /\ Q # {}) {
                           with (p \in Q) {
                              MaybeFail();   \* the node can crash when sending message
                              if (~up[self]) {      \* if the node crash, it's terminated
                                  t[self] := TRUE;
                                  goto PR;
                              }
                              else {
                                  mb[p] := mb[p] \union {v};    \* put value v into the node's mailbox
                                  Q := Q \ {p};                 \* delete p out of the set Q
                              }
                           };
                       };
                   }
                   else {
                        await (\A i \in Nodes : pt[i] >=1 \/ ~up[i]);   \* for all nodes, if not at at round 0, or up[i] = Fasle
                        Q := Nodes;
                        L2: while (up[self] /\ Q # {}) {
                           with (p \in Q) {
                              MaybeFail();
                              if (~up[self]) {
                                  t[self] := TRUE;
                                  goto PR;
                              }
                              else {
                                  mb[p] := mb[p] \union mb[self];
                                  Q := Q \ {p};
                              }
                           };
                        };
                   };
                   L3: pt[self] := pt[self] + 1;
               };
               
           PR: await (\A n \in Nodes : (pt[n] = counter+1 \/ up[n] = FALSE));  \* await for all nodes at rounds counter+1 or up[n] = False
               if (up[self]) d[self] := SetMin(mb[self]);
               t[self] := TRUE;
        }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, pt, t, d, mb, pc

(* define statement *)
SetMin(S) == CHOOSE i \in S : \A j \in S : i <= j

VARIABLES v, Q

vars == << FailNum, up, pt, t, d, mb, pc, v, Q >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [ n \in Nodes |-> {}]
        (* Process n *)
        /\ v = [self \in Nodes |-> 0]
        /\ Q = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF up[self]
                 THEN /\ v' = [v EXCEPT ![self] = self]
                      /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ pc' = [pc EXCEPT ![self] = "PS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << v, Q >>
           /\ UNCHANGED << FailNum, up, pt, t, d, mb >>

PS(self) == /\ pc[self] = "PS"
            /\ IF pt[self] <= counter
                  THEN /\ IF pt[self] = 0
                             THEN /\ Q' = [Q EXCEPT ![self] = Nodes]
                                  /\ pc' = [pc EXCEPT ![self] = "L1"]
                             ELSE /\ (\A i \in Nodes : pt[i] >=1 \/ ~up[i])
                                  /\ Q' = [Q EXCEPT ![self] = Nodes]
                                  /\ pc' = [pc EXCEPT ![self] = "L2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ Q' = Q
            /\ UNCHANGED << FailNum, up, pt, t, d, mb, v >>

L3(self) == /\ pc[self] = "L3"
            /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "PS"]
            /\ UNCHANGED << FailNum, up, t, d, mb, v, Q >>

L1(self) == /\ pc[self] = "L1"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ IF FailNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum - 1
                                             /\ counter' = counter+1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                            /\ IF ~up'[self]
                                  THEN /\ t' = [t EXCEPT ![self] = TRUE]
                                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                                       /\ UNCHANGED << mb, Q >>
                                  ELSE /\ mb' = [mb EXCEPT ![p] = mb[p] \union {v[self]}]
                                       /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                                       /\ pc' = [pc EXCEPT ![self] = "L1"]
                                       /\ t' = t
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L3"]
                       /\ UNCHANGED << FailNum, up, t, mb, Q >>
            /\ UNCHANGED << pt, d, v >>

L2(self) == /\ pc[self] = "L2"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ IF FailNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum - 1
                                             /\ counter' = counter+1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                            /\ IF ~up'[self]
                                  THEN /\ t' = [t EXCEPT ![self] = TRUE]
                                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                                       /\ UNCHANGED << mb, Q >>
                                  ELSE /\ mb' = [mb EXCEPT ![p] = mb[p] \union mb[self]]
                                       /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                                       /\ pc' = [pc EXCEPT ![self] = "L2"]
                                       /\ t' = t
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L3"]
                       /\ UNCHANGED << FailNum, up, t, mb, Q >>
            /\ UNCHANGED << pt, d, v >>

PR(self) == /\ pc[self] = "PR"
            /\ (\A n \in Nodes : (pt[n] = counter+1 \/ up[n] = FALSE))
            /\ IF up[self]
                  THEN /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
                  ELSE /\ TRUE
                       /\ d' = d
            /\ t' = [t EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << FailNum, up, pt, mb, v, Q >>

n(self) == P(self) \/ PS(self) \/ L3(self) \/ L1(self) \/ L2(self)
              \/ PR(self)

Next == (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
Inv == (\E i \in Nodes : ~t[i]) \/ (\A l,m \in Nodes : ~up[l] \/ ~up[m] \/ d[l] = d[m])
=============================================================================
\* Modification History
\* Last modified Tue Oct 24 15:27:38 EDT 2017 by xinboyu
\* Last modified Tue Oct 24 15:17:22 EDT 2017 by kz-pc
\* Created Tue Oct 24 14:42:35 EDT 2017 by kz-pc
