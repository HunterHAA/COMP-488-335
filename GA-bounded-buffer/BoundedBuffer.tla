-------------------------------- MODULE BoundedBuffer --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC

CONSTANTS producers, consumers, BufferSize 
          
ASSUME /\ producers > 0
       /\ consumers > 0
       /\ BufferSize > 0
       
put(bufferSize, s) == Append(bufferSize, s)
get(bufferSize) == Tail(bufferSize)

(*
--algorithm BoundedBuffer {
    variables bufferSize = <<>>, processing=0;         
  
 
   process(p \in 1..producers) {
      p0:
        while(processing < 100) {
           either {
              p1:
                when Len(bufferSize) < BufferSize;
                processing := processing +1;
                bufferSize := Append(bufferSize, processing);
           }
           or {
              p2: skip;
           }
        };
   }
   
   process(c \in 5..consumers+5) {
      c0:
         while(processing < 100) {
               either {
                  c1:
                    when Len(bufferSize) > 0;
                    bufferSize := Tail(bufferSize);
                    processing := processing +1;
               }
               or {
                  c2: skip;
               }
         };
   } 
 

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "157a1b47" /\ chksum(tla) = "6ec90254")
VARIABLES bufferSize, processing, pc

vars == << bufferSize, processing, pc >>

ProcSet == (1..producers) \cup (5..consumers+5)

Init == (* Global variables *)
        /\ bufferSize = <<>>
        /\ processing = 0
        /\ pc = [self \in ProcSet |-> CASE self \in 1..producers -> "p0"
                                        [] self \in 5..consumers+5 -> "c0"]

p0(self) == /\ pc[self] = "p0"
            /\ IF processing < 100
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "p1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << bufferSize, processing >>

p1(self) == /\ pc[self] = "p1"
            /\ Len(bufferSize) < BufferSize
            /\ processing' = processing +1
            /\ bufferSize' = Append(bufferSize, processing')
            /\ pc' = [pc EXCEPT ![self] = "p0"]

p2(self) == /\ pc[self] = "p2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << bufferSize, processing >>

p(self) == p0(self) \/ p1(self) \/ p2(self)

c0(self) == /\ pc[self] = "c0"
            /\ IF processing < 100
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "c1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "c2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << bufferSize, processing >>

c1(self) == /\ pc[self] = "c1"
            /\ Len(bufferSize) > 0
            /\ bufferSize' = Tail(bufferSize)
            /\ processing' = processing +1
            /\ pc' = [pc EXCEPT ![self] = "c0"]

c2(self) == /\ pc[self] = "c2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "c0"]
            /\ UNCHANGED << bufferSize, processing >>

c(self) == c0(self) \/ c1(self) \/ c2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..producers: p(self))
           \/ (\E self \in 5..consumers+5: c(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
