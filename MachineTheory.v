Require Import StateMachines.Preliminaries.
Require Import StateMachines.Concepts.
Import ListNotations.
Import MACHINE.

Section MachineTheory.
Variable m : Machine.

(* Rest law *)
Definition act0 (f : state m → list (input m) → state m)
:= ∀ s : state m, f s [] = s.
(* Single impact law *)
Definition act1 (f : state m → list (input m) → state m)
:= ∀ (s : state m) (i : input m), f s [i] = pass m s i.
(* Cumulative law *)
Definition actC (f : state m → list (input m) → state m)
:= ∀ (s : state m) (u' u'' : list (input m)),
     f s (u' ++ u'') = f (f s u') u''.

Lemma run0 : act0 (run m).
Proof. unfold act0. trivial. Qed.

Lemma run1 : act1 (run m).
Proof. unfold act1. trivial. Qed.

Lemma runC : actC (run m).
Proof.
  unfold actC. intros. revert s.
  induction u' as [| i v IHu']; intro; simpl.
  - reflexivity.
  - exact (IHu' (pass m s i)).
Qed.

Section UniquenessTheorem.
Variable run' : state m → list (input m) → state m. 
Hypotheses (H0 : act0 run')
           (H1 : act1 run')
           (HC : actC run').

Theorem run_uniqueness : ∀ (s : state m) (u : list (input m)),
  run' s u = run m s u.
Proof.
  intros. revert s.
  induction u as [| i u' IHu]; intro; simpl.
  - apply H0.
  - assert (H : [i] ++ u' = i :: u'). { trivial. }
    rewrite <- H. rewrite (HC s [i] u').
    rewrite <- (H1 s). apply IHu.
Qed.
End UniquenessTheorem.
End MachineTheory.
