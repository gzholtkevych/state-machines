Require Import StateMachines.Preliminaries.
Import ListNotations.
Require Import StateMachines.Concepts.


Definition mover := mkMachine bool nat
                              (fun s i => match i with true  => s
                                                     | false => S s end) _.


Compute run mover 0 [true; false; true; true; false].

Definition even : Acceptor
:= mkAcceptor mover
              (fix f s := match s with
                          | 0    => True
                          | S s' => match s' with 0     => False
                                                | S s'' => f s'' end
                          end).

Compute acceptable even 0 [true; false; true; false; true].
Compute acceptable even 0 [true; false; true; false; false; true].

Inductive rgb : Set :=
| red : rgb
| green : rgb
| blue : rgb.

Instance rgb_fin_cert : Finitary rgb.
Admitted.