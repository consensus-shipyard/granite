------------------- MODULE GraniteBC -------------------
EXTENDS Bags, FiniteSets, Integers, Sequences, TLC

CONSTANTS 
    NIL,    \* The nil value
    COIN   \* Value of coin flip

N == 1..4        \* The set of all processes.
TotalRounds == 1            \* The total number of rounds of message exchanges.
\*LuckyRound == TotalRounds-1 \* The round in which all processes flip the same coin.

(* Algorithm steps *)
Step_1 == 1
Step_2 == 2
Step_3 == 3

(* Arithmetic for n and optimal f. *)
n == Cardinality(N)
f == CHOOSE f \in 1..n: n = 3*f+1

(* The set of Byzantine processes *)
Byzantine == {p \in N: p > n - f}

(* The set of correct processes *)
Correct == {p \in N: p <= n - f}

(* Message construction. *)
Msg(round, step, value, sender) ==
    [round |-> round, step |-> step, value |-> value, sender |-> sender]

(* Adds a message 'msg' to the set of messages 'msgs' ever sent to the network. *)
Broadcast(msgs, msg) == msgs \union {msg}

(* All subsets of the subset of `msgs` for a particular round and step with cardinality 2f+1. *) 
DeliverMsgs(msgs, round, step) ==
    {M \in SUBSET {m \in msgs: m.round = round /\ m.step = step}:
        Cardinality(M) = 2*f+1 /\ (\A <<m1, m2>> \in M \X M: m1 # m2 => m1.sender # m2.sender)}

(* Whether there are n messages in the set msgs for a particular round and step. *)
AllMessages(msgs, round, step) ==
    Cardinality({ m.sender: m \in {m \in msgs: m.round = round /\ m.step = step} }) = n

(* A bag of values from a set of messages. *)
Values(M) == BagOfAll(LAMBDA m: m.value, SetToBag(M))

(* The most frequently ocurring element in a bag. *)
Mode(B) == CHOOSE x \in BagToSet(B): (\A y \in BagToSet(B): B[x] >= B[y]) 

(* Whether some value not NIL occurs `threshold` or more times in a set of messages M.  *)
SomeHasCount(M, threshold) ==
    LET B == Values(M)
    IN \E v \in (BagToSet(B) \ {NIL}): B[v] >= threshold 

(* Choose a value not NIL in a set of messages M that occurs `threshold` or more times. *)
ChooseValue(M, threshold) ==    
    LET B == Values(M)
    IN CHOOSE v \in (BagToSet(B) \ {NIL}): B[v] >= threshold 

ValueFunctionStep1(M) == Mode(Values(M))

ValueFunctionStep2(M) ==
    IF SomeHasCount(M, 2*f+1)
    THEN ChooseValue(M, 2*f+1)
    ELSE NIL

ValueFunctionStep3(M) == 
    IF SomeHasCount(M, 2*f+1)
    THEN ChooseValue(M, 2*f+1)
    ELSE
        IF SomeHasCount(M, 1)
        THEN ChooseValue(M, 1)
        ELSE COIN

ValueFunction(step, M) == 
    CASE step = 1 -> ValueFunctionStep1(M)
      [] step = 2 -> ValueFunctionStep2(M)
      [] step = 3 -> ValueFunctionStep3(M)
      [] OTHER -> NIL

(* --algorithm GraniteBC
variables
    (* The set of all messages broadcast to the network. *)
    msgs = {},
(* Main body of the algorithm. *)
fair process group \in N
variables 
    round = 1,
    initial \in {0, 1},
    value = NIL,
    decided = FALSE
begin
    initial_broadcast:
    if self \in Byzantine then 
        msgs := { Msg(round, Step_1, v, self): v \in {0, 1} } \union msgs;
    else
        msgs := Broadcast(msgs, Msg(round, Step_1, initial, self)) \union msgs;
    end if;

    loop:
    while round <= TotalRounds do
        step_1:
        await AllMessages(msgs, round, 1); 
        if self \in Byzantine then
            msgs := { Msg(round, Step_2, ValueFunctionStep1(M), self): M \in DeliverMsgs(msgs, round, Step_1) } \union msgs;
        else
            with M \in DeliverMsgs(msgs, round, Step_1) do             
                value := ValueFunctionStep1(M);            
            end with;
            msgs := { Msg(round, Step_2, value, self) } \union msgs;
        end if;

        step_2:
        await AllMessages(msgs, round, Step_2); 
        if self \in Byzantine then
            msgs := { Msg(round, Step_3, ValueFunctionStep2(M), self): M \in DeliverMsgs(msgs, round, Step_2) } \union msgs;
        else
            with M \in DeliverMsgs(msgs, round, 2) do             
                value := ValueFunctionStep2(M);            
            end with;
            msgs := { Msg(round, Step_3, value, self) } \union msgs;
        end if;

        step_3:
        await AllMessages(msgs, round, Step_3); 
        if self \in Byzantine then
            msgs := { Msg(round+1, Step_1, ValueFunctionStep3(M), self): M \in DeliverMsgs(msgs, round, Step_3) } \union msgs;
        else
            with M \in DeliverMsgs(msgs, round, Step_3) do             
                value := ValueFunctionStep3(M);
                decided := SomeHasCount(M, 2*f+1);

                \*if round < LuckyRound then
                \*    (* Nondeterministic choice. *)
                \*    with v \in {0, 1} do
                \*        value := v;
                \*    end with;
                \*else
                    (*
                     * In our lucky round, we inspect all messages and choose
                     * in a way that ensure unanimity (or quasi-unanimity).
                     *)
                \*    value := LET All == {m \in msgs: m.sender \in Correct /\ m.round = round /\ m.step = Step_3}
                \*             IN IF SomeHasCount(All, 1)
                \*                THEN ChooseValue(All, 1)
                \*                ELSE 1;
                \*end if;                

            end with;        
            msgs := { Msg(round+1, Step_1, value, self) } \union msgs;
        end if;

        round := round + 1;
    end while;

end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "f0cba5c7" /\ chksum(tla) = "1d868748")
VARIABLES msgs, pc, round, initial, value, decided

vars == << msgs, pc, round, initial, value, decided >>

ProcSet == (N)

Init == (* Global variables *)
        /\ msgs = {}
        (* Process group *)
        /\ round = [self \in N |-> 1]
        /\ initial \in [N -> {0, 1}]
        /\ value = [self \in N |-> NIL]
        /\ decided = [self \in N |-> FALSE]
        /\ pc = [self \in ProcSet |-> "initial_broadcast"]

initial_broadcast(self) == /\ pc[self] = "initial_broadcast"
                           /\ IF self \in Byzantine
                                 THEN /\ msgs' = ({ Msg(round[self], Step_1, v, self): v \in {0, 1} } \union msgs)
                                 ELSE /\ msgs' = (Broadcast(msgs, Msg(round[self], Step_1, initial[self], self)) \union msgs)
                           /\ pc' = [pc EXCEPT ![self] = "loop"]
                           /\ UNCHANGED << round, initial, value, decided >>

loop(self) == /\ pc[self] = "loop"
              /\ IF round[self] <= TotalRounds
                    THEN /\ pc' = [pc EXCEPT ![self] = "step_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << msgs, round, initial, value, decided >>

step_1(self) == /\ pc[self] = "step_1"
                /\ AllMessages(msgs, round[self], 1)
                /\ IF self \in Byzantine
                      THEN /\ msgs' = ({ Msg(round[self], Step_2, ValueFunctionStep1(M), self): M \in DeliverMsgs(msgs, round[self], Step_1) } \union msgs)
                           /\ value' = value
                      ELSE /\ \E M \in DeliverMsgs(msgs, round[self], Step_1):
                                value' = [value EXCEPT ![self] = ValueFunctionStep1(M)]
                           /\ msgs' = ({ Msg(round[self], Step_2, value'[self], self) } \union msgs)
                /\ pc' = [pc EXCEPT ![self] = "step_2"]
                /\ UNCHANGED << round, initial, decided >>

step_2(self) == /\ pc[self] = "step_2"
                /\ AllMessages(msgs, round[self], Step_2)
                /\ IF self \in Byzantine
                      THEN /\ msgs' = ({ Msg(round[self], Step_3, ValueFunctionStep2(M), self): M \in DeliverMsgs(msgs, round[self], Step_2) } \union msgs)
                           /\ value' = value
                      ELSE /\ \E M \in DeliverMsgs(msgs, round[self], 2):
                                value' = [value EXCEPT ![self] = ValueFunctionStep2(M)]
                           /\ msgs' = ({ Msg(round[self], Step_3, value'[self], self) } \union msgs)
                /\ pc' = [pc EXCEPT ![self] = "step_3"]
                /\ UNCHANGED << round, initial, decided >>

step_3(self) == /\ pc[self] = "step_3"
                /\ AllMessages(msgs, round[self], 3)
                /\ IF self \in Byzantine
                      THEN /\ msgs' = ({ Msg(round[self]+1, Step_1, ValueFunctionStep3(M), self): M \in DeliverMsgs(msgs, round[self], Step_3) } \union msgs)
                           /\ UNCHANGED << value, decided >>
                      ELSE /\ \E M \in DeliverMsgs(msgs, round[self], Step_3):
                                /\ value' = [value EXCEPT ![self] = ValueFunctionStep3(M)]
                                /\ decided' = [decided EXCEPT ![self] = SomeHasCount(M, 2*f+1)]
                           /\ msgs' = ({ Msg(round[self]+1, Step_1, value'[self], self) } \union msgs)
                /\ round' = [round EXCEPT ![self] = round[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "loop"]
                /\ UNCHANGED initial

group(self) == initial_broadcast(self) \/ loop(self) \/ step_1(self)
                  \/ step_2(self) \/ step_3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in N: group(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in N : WF_vars(group(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

(** Invariants **)
\* Agreement == \A <<p1, p2>> \in N \X N: decision[p1] # NIL => (decision[p1] = decision[p2] \/ decision[p2] = NIL)
\* StrongTermination == \A p \in N: round[p] > TotalRounds => decision[p] # NIL
Agreement ==
    (\A p \in N: pc[p] = "Done") => (
        \A <<p1, p2>> \in Correct \X Correct:
            (value[p1] \in {0,1} => (value[p1] = value[p2] \/ value[p2] = COIN))
    )

UnanimityImpliesTermination ==
    (\A p \in N: pc[p] = "Done") => (
        (\A <<p1, p2>> \in Correct \X Correct: initial[p1] = initial[p2]) =>
            (\A p \in Correct: decided[p] /\ value[p] = initial[p])
    )

DecisionImpliesDeterministicChoice ==
    (\A p \in N: pc[p] = "Done") => (
        \A <<p1, p2>> \in Correct \X Correct: 
            (decided[p1] => (value[p1] \in {0,1} /\ value[p1] = value[p2]))
    )

=============================================================================
\* Modification History
\* Last modified Thu Nov 17 12:32:13 WET 2022 by hmz
\* Created Wed Nov 16 09:30:58 WET 2022 by hmz
