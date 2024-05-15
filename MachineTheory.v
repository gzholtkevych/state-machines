Require Import StateMachines.Preliminaries.
Require Import StateMachines.Concepts.
Import ListNotations.

Section MachineTheory.
Variable m : Machine.

  (* Rest law *)
  Definition act0 (f : Q m → list (A m) → Q m) := 
    ∀ s : Q m, f s [] = s.
  (* Single impact law *)
  Definition act1 (f : Q m → list (A m) → Q m) :=
    ∀ (q : Q m) (a : A m), f q [a] = do m q a.
  (* Cumulative law *)
  Definition actC (f : Q m → list (A m) → Q m) := 
    ∀ (q : Q m) (u' u'' : list (A m)),
      f q (u' ++ u'') = f (f q u') u''.

  Lemma run0 : act0 run.
  Proof. unfold act0. trivial. Qed.

  Lemma run1 : act1 run.
  Proof. unfold act1. trivial. Qed.

  Lemma runC : actC run.
  Proof.
    unfold actC. intros. revert q.
    induction u' as [| a v IHu']; intro; simpl.
    - reflexivity.
    - exact (IHu' (do m q a)).
  Qed.

  Section UniquenessTheorem.
  Variable run' : Q m → list (A m) → Q m. 
  Hypotheses (H0 : act0 run')
             (H1 : act1 run')
             (HC : actC run').

    Theorem run_uniqueness : ∀ (q : Q m) (u : list (A m)), run' q u = run q u.
    Proof.
      intros. revert q.
      induction u as [| a u' IHu]; intro; simpl.
      - apply H0.
      - assert (H : [a] ++ u' = a :: u'). { trivial. }
        rewrite <- H. rewrite (HC q [a] u').
        rewrite <- (H1 q). apply IHu.
    Qed.

  End UniquenessTheorem.

  

End MachineTheory.
