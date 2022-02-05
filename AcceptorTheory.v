Require Import StateMachines.Preliminaries.
Require Import StateMachines.Concepts.
Require Import StateMachines.MachineTheory.
Import ListNotations.

Section AcceptorTheory.
Variables (m : Machine) (a : @Acceptor m).

Definition acc0 (f : state m → list (input m) → Prop)
:= ∀ s : state m, f s [] ↔ acceptant a s.
Definition accT (f : state m → list (input m) → Prop)
:= ∀ (s : state m) (u' u'' : list (input m)),
     f s (u' ++ u'') ↔ f (run m s u') u''.


Lemma acceptable0 : acc0 (acceptable a).
Proof. unfold acc0. intro. split; trivial. Qed.

Lemma acceptableT : accT (acceptable a).
Proof.
  unfold accT. intros. split; revert s.
  - induction u' as [| i v IHu].
    + trivial.
    + intro. apply IHu.
  - intro. pose (runC := runC m s u' u'').
    unfold acceptable. now rewrite <- runC.
Qed.

Section UniquenessTheorem.
Variable acceptable' : state m → list (input m) → Prop. 
Hypotheses (H0 : acc0 acceptable')
           (HT : accT acceptable').

Theorem acceptable_uniqueness : ∀ (s : state m) (u : list (input m)),
  acceptable' s u ↔ acceptable a s u.
Proof.
  intros. revert s.
  induction u as [| i u' IHu]; intro; simpl.
  - apply H0.
  - assert (H : [i] ++ u' = i :: u'). { trivial. }
    rewrite <- H.
    split; intro; elim (HT s [i] u'); intros.
    + apply (IHu (pass m s i)). rewrite run1 in H2.
      now apply H2.
    + apply H3. apply IHu. unfold acceptable in H1. simpl in H1. assumption.
Qed.
End UniquenessTheorem.
End AcceptorTheory.