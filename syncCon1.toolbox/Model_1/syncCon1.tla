------------------------------ MODULE syncCon1 ------------------------------
\*zheng kai 50247576
\*xuyin bo  50102922
\* Synchronized Consensus
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, FAILNUM
ASSUME N <= 5 /\ 0 <= FAILNUM /\ FAILNUM <= 4
Nodes == 1 .. N

(*
--algorithm syncCon1 {
    variables FailNum = FAILNUM;           \* Initialization block
              up = [n \in Nodes |-> TRUE]; \* Nodes are up
              pt = [n \in Nodes |-> 0];    \* Nodes are at round 0
              t = [n \in Nodes |-> FALSE]; \* Nodes are not terminated
              d = [n \in Nodes |-> -1];    \* Nodes are not decided
              mb = [ n \in Nodes |-> {}];  \* Nodes have mailbox as emptyset
              
    define {
        SetMin(S) == CHOOSE i \in S : \A j \in S : i <= j  \* choose the smallest value in S
    }
    
    macro MaybeFail() {
        if (FailNum > 0 /\ up[self])
        {
            either 
            { up[self] := FALSE; FailNum := FailNum - 1; }
            or skip;
        }
    }
    
    fair process(n \in Nodes)
    variables v = 0, Q = {};
    {
            P: if (up[self]) {
                    v := self;
                    Q := Nodes;
            PS: while (up[self] /\ Q # {}) {
                   with (p \in Q) {
                          MaybeFail();       \* the node can crash when sending message            
                          mb[p] := mb[p] \union{v};      \* put value v into the node's mailbox                     
                          Q :=  Q \ {p} ;       \* delete p out of the set Q                   
                   };
               };
               if (up[self]) pt[self] := pt[self] + 1;
           PR: await (up[self]) /\ (\A i \in Nodes : (pt[i] = 1 \/ up[i] = FALSE)); \* wait for all nodes receive others' message
               d[self] := SetMin(mb[self]);   \* use SetMin() function to decide the smallest value in collection
               t[self] := TRUE;                \* when the node has decide the smallest value, it's done.
               
        };
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
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ IF FailNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum - 1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                            /\ mb' = [mb EXCEPT ![p] = mb[p] \union{v[self]}]
                            /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                       /\ pc' = [pc EXCEPT ![self] = "PS"]
                       /\ pt' = pt
                  ELSE /\ IF up[self]
                             THEN /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
                             ELSE /\ TRUE
                                  /\ pt' = pt
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << FailNum, up, mb, Q >>
            /\ UNCHANGED << t, d, v >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self]) /\ (\A i \in Nodes : (pt[i] = 1 \/ up[i] = FALSE))
            /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
            /\ t' = [t EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << FailNum, up, pt, mb, v, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

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
\* 1.2 Model-check safety properties with TLA+
\* First, we assume no crash. It means after this round, every node sends it value to others and decide the smallest value. 
\* So at the model check, we set FailNum = 0, Nodes = 5, choose the termination property and there is no error.
\* Then change the FailNum to 1,2,3,4, Node still equals 5, choose the termination property, then error happens.
\* For examle, node1 crash when only node2 receive it's value. Assume others node don't crash and program still run,
\* Then node2 set the min value = 1, but node3,node4,node5 can not set min value = 1. So this consensus protocol algorithm does't work.
\* And at this algorithm, when node1 crash, up[1] will be False. So the termination property will be violated.
\* So the agreement property satisfied when FailNum = 0, unsatisfied when FailNum > 0 
\* Then test an invariant property Inv == (\E i \in Nodes : ~t[i]) \/ (\A l,m \in Nodes : ~up[l] \/ ~up[m] \/ d[l] = d[m])
\* An invariant property should be satisfied at every situations. So check the invariant property when FailNum from 0 to 4. It maintains right.

\* Modification History
\* Last modified Tue Oct 24 15:24:46 EDT 2017 by xinboyu
\* Last modified Tue Oct 24 11:58:03 EDT 2017 by kz-pc
\* Created Sat Oct 21 11:02:18 EDT 2017 by kz-pc
