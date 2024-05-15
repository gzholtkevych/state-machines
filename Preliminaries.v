Require Export Utf8.
Require Export Lists.List.
Export ListNotations.


Structure Alphabet : Type := alphabet {
  letter :> Set;
  eq_neq_dec : ∀ a b : letter, {a = b} + {a ≠ b};
  fin_evidence : {enum : list letter | ∀ a : letter, In a enum}
}.