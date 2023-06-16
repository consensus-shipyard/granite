------------------- MODULE GraniteBC -------------------
EXTENDS Bags, FiniteSets, Integers, Sequences, TLC

CONSTANTS 
    NIL,    \* The nil value
    COIN   \* Value of coin flip

N == 1..4        \* The set of all processes.
TotalRounds == 1            \* The total number of rounds of message exchanges.
LuckyRound == TotalRounds-1 \* The round in which all processes flip the same coin.

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
Bcast(msgs, msg) == msgs \union {msg}

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

macro ComputeStep3() begin
    with M \in DeliverMsgs(msgs, round, 3) do
        (* 
        * If we receive 2f+1 messages with the same value not NIL, then we
        * decide that value.
        *)
        if SomeHasCount(M, 2*f+1) then                
            decided := TRUE;
        end if;

        (*
        * If we receive f+1 messages with the same value not NIL, then we
        * set our proposal to that value.
        *)
        if SomeHasCount(M, f+1) then
            Value := {ChooseValue(M, f+1)};

        (*
        * Otherwise, if we only receive one message with some value v not
        * NIL, then we choose our proposal value randomly as a coin flip
        * between v and min.
        * To model this, we assume that exists a "lucky" round where all
        * processes flip the right value. In all other rounds, we choose
        * nondeterministically between v and min.
        *)
        else         
            if round < LuckyRound then
                (* Nondeterministic choice. *)
                with v \in {0, 1} do
                    Value := {v};
                end with;
            else
                (*
                * In our lucky round, we inspect all messages and choose
                * in a way that ensures unanimity among correct processes.
                *)
                Value := LET All == {m \in msgs: m.sender \in Correct /\ m.round = round /\ m.step = Step_3}
                            IN IF SomeHasCount(All, 1)
                            THEN {ChooseValue(All, 1)}
                            ELSE {1};
            end if;
        end if;
    end with;
end macro;

(* Main body of the algorithm. *)
fair process group \in N
variables 
    round = 1,
    step = 1,
    initial \in {0, 1},
    Value = {},
    decided = FALSE,
begin
    initial_value:
    Value := IF self \in Byzantine THEN {0, 1} ELSE {initial};

    loop:
    while round <= TotalRounds do        
        broadcast:
        if self \in Byzantine then 
            msgs := msgs \union { Msg(round, step, v, self): v \in Value };
        else
            with v \in Value do 
                msgs := msgs \union { Msg(round, step, v, self) };
            end with;
        end if;

        step:
        await AllMessages(msgs, round, step);
        if self \in Byzantine then 
            Value := { ValueFunction(step, M): M \in DeliverMsgs(msgs, round, step) };
        else
            with M \in DeliverMsgs(msgs, round, step) do 
                Value := { ValueFunction(step, M) };
                decided := step = 3 /\ SomeHasCount(M, 2*f+1);
            end with;
        end if;

        next_step:
        if step < 3 then 
            step := step +1;
        else
            step := 1;
            round := round + 1;
        end if;
    end while;

end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "531ccd4f" /\ chksum(tla) = "62288bc1")
\* Label step of process group at line 154 col 9 changed to step_
VARIABLES msgs, pc, round, step, initial, Value, decided

vars == << msgs, pc, round, step, initial, Value, decided >>

ProcSet == (N)

Init == (* Global variables *)
        /\ msgs = {}
        (* Process group *)
        /\ round = [self \in N |-> 1]
        /\ step = [self \in N |-> 1]
        /\ initial \in [N -> {0, 1}]
        /\ Value = [self \in N |-> {}]
        /\ decided = [self \in N |-> FALSE]
        /\ pc = [self \in ProcSet |-> "initial_value"]

initial_value(self) == /\ pc[self] = "initial_value"
                       /\ Value' = [Value EXCEPT ![self] = IF self \in Byzantine THEN {0, 1} ELSE {initial[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "loop"]
                       /\ UNCHANGED << msgs, round, step, initial, decided >>

loop(self) == /\ pc[self] = "loop"
              /\ IF round[self] <= TotalRounds
                    THEN /\ pc' = [pc EXCEPT ![self] = "broadcast"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << msgs, round, step, initial, Value, decided >>

broadcast(self) == /\ pc[self] = "broadcast"
                   /\ IF self \in Byzantine
                         THEN /\ msgs' = (msgs \union { Msg(round[self], step[self], v, self): v \in Value[self] })
                         ELSE /\ \E v \in Value[self]:
                                   msgs' = (msgs \union { Msg(round[self], step[self], v, self) })
                   /\ pc' = [pc EXCEPT ![self] = "step_"]
                   /\ UNCHANGED << round, step, initial, Value, decided >>

step_(self) == /\ pc[self] = "step_"
               /\ AllMessages(msgs, round[self], step[self])
               /\ IF self \in Byzantine
                     THEN /\ Value' = [Value EXCEPT ![self] = { ValueFunction(step[self], M): M \in DeliverMsgs(msgs, round[self], step[self]) }]
                          /\ UNCHANGED decided
                     ELSE /\ \E M \in DeliverMsgs(msgs, round[self], step[self]):
                               /\ Value' = [Value EXCEPT ![self] = { ValueFunction(step[self], M) }]
                               /\ decided' = [decided EXCEPT ![self] = step[self] = 3 /\ SomeHasCount(M, 2*f+1)]
               /\ pc' = [pc EXCEPT ![self] = "next_step"]
               /\ UNCHANGED << msgs, round, step, initial >>

next_step(self) == /\ pc[self] = "next_step"
                   /\ IF step[self] < 3
                         THEN /\ step' = [step EXCEPT ![self] = step[self] +1]
                              /\ round' = round
                         ELSE /\ step' = [step EXCEPT ![self] = 1]
                              /\ round' = [round EXCEPT ![self] = round[self] + 1]
                   /\ pc' = [pc EXCEPT ![self] = "loop"]
                   /\ UNCHANGED << msgs, initial, Value, decided >>

group(self) == initial_value(self) \/ loop(self) \/ broadcast(self)
                  \/ step_(self) \/ next_step(self)

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
    \A <<p1, p2>> \in Correct \X Correct: decided[p1] /\ decided[p2] => Value[p1] = Value[p2]

UnanimityImpliesTermination ==
    (\A p \in N: pc[p] = "Done") => (
        (\A <<p1, p2>> \in Correct \X Correct: initial[p1] = initial[p2]) =>
            (\A p \in Correct: decided[p] /\ Value[p] = {initial[p]})
    )

DecisionImpliesDeterministicChoice ==
    (\A p \in N: pc[p] = "Done") => (
        \A <<p1, p2>> \in Correct \X Correct: 
            (decided[p1] => (Value[p1] \in {{0},{1}} /\ Value[p1] = Value[p2]))
    )

=============================================================================
\* Modification History
\* Last modified Thu Nov 17 12:32:13 WET 2022 by hmz
\* Created Wed Nov 16 09:30:58 WET 2022 by hmz
