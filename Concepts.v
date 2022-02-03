Require Import StateMachines.Preliminaries.
Import ListNotations.


Module MACHINE.
Structure Machine := mkMachine
{ input : Set
; state : Set
; pass : state → input → state
; input_fin_cert : Finitary input
}.
Fixpoint run (m : Machine)
           (s : state m)
           (u : list (input m))
:= match u with []      => s
              | i :: u' => run m (pass m s i) u' end.
End MACHINE.


Module ACCEPTOR.
Import MACHINE.
Structure Acceptor {m : Machine} := mkAcceptor
{ acceptant : state m → Prop }.
Definition acceptable {m : Machine}
             (a : Acceptor)
             (s : state m) : list (input m) → Prop
:= fun u => acceptant a (run m s u).
End ACCEPTOR.


Module TRANSDUCER.
Import MACHINE.
Structure Transducer {m : Machine} := mkTransducer
{ output : Set
; response : state m → output
; output_fin_cert : Finitary output
}.

End TRANSDUCER.