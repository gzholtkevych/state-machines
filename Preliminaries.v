Require Export Utf8.
Require Export Lists.List.
Export ListNotations.


Class Finitary (T : Type) : Prop :=
fin_cert : ∃ e : list T, ∀ x : T, In x e.

Instance bool_fin_cert : Finitary bool.
Proof.
  exists [true; false]. intro.
  case x; [now left | right]; now left.
Qed.