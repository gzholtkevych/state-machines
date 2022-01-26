Require Import StateMachines.Preliminaries.
Import ListNotations.
Require Import StateMachines.Concepts.
Import MACHINE.
Import ACCEPTOR.


Definition mover : Machine
:= {| state := nat; input := bool;
      pass := fun s i => match i with true  => s
                                    | false => S s end |}.

Compute run mover 0 [true; false; true; true; false].

Definition even : Acceptor
:= mkAcceptor mover
               (fix f s := match s with
                           | 0    => True
                           | S s' => match s' with 0     => False
                                                 | S s'' => f s'' end
                           end).

Compute accept even 0 [true; false; true; false; true].
Compute accept even 0 [true; false; true; false; false; true].

Inductive rgb : Set :=
| red : rgb
| green : rgb
| blue : rgb.

Instance rgb_fin_cert : Finitary rgb.
Admitted.