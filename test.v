Definition D: Prop := forall A: Prop, forall B: Prop, (A <-> B) -> (A -> B).

Set Printing All.
Print D.

Theorem tD: D.
  intros A B h a.