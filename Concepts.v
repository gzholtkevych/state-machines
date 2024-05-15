Require Import StateMachines.Preliminaries.
Import ListNotations.


Structure Machine := machine
{ A : Alphabet
; Q : Set
; do : Q → A → Q
}.
Fixpoint run {m : Machine}
             (q : Q m)
             (u : list (A m))
:= match u with []      => q
              | a :: u' => run (do m q a) u' end.

(*
Module ACCEPTOR.
Structure Acceptor {m : MACHINE.Machine} := mkAcceptor
{ acceptant : MACHINE.Q m → bool }.
Definition acceptable {m : MACHINE.Machine}
             (a : Acceptor)
             (s : MACHINE.state m) : list (MACHINE.input m) → Prop
:= fun u => acceptant a (MACHINE.run m s u).
End ACCEPTOR.


Module TRANSDUCER.
Import MACHINE.
Structure Transducer {m : Machine} := mkTransducer
{ output : Set
; response : state m → output
; output_fin_cert : Finitary output
}.

End TRANSDUCER.

Notation Machine := MACHINE.Machine               (only parsing).
Notation mkMachine := MACHINE.mkMachine           (only parsing).
Notation input := MACHINE.input                   (only parsing).
Notation state := MACHINE.state                   (only parsing).
Notation pass := MACHINE.pass                     (only parsing).
Notation run := MACHINE.run                       (only parsing).
Notation Acceptor := ACCEPTOR.Acceptor            (only parsing).
Notation mkAcceptor := ACCEPTOR.mkAcceptor        (only parsing).
Notation acceptant := ACCEPTOR.acceptant          (only parsing).
Notation acceptable := ACCEPTOR.acceptable        (only parsing).
*)