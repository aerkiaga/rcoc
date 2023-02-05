Inductive my_nat := my_O : my_nat | my_S : my_nat -> my_nat.

Print my_nat.

Definition foo: my_nat -> my_nat := fun x: my_nat => match x with
  | my_O => my_O
  | my_S _ => my_S my_O
  end
.

Print foo.