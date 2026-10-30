(** * Syntax: fragment formulas (1, ⊗, ⊸, ⊕, ◇ₖ) *)

Inductive form : Type :=
| Atom   : nat -> form
| One    : form
| Tensor : form -> form -> form
| Lolli  : form -> form -> form
| Plus   : form -> form -> form
| Dia    : nat -> form -> form.   (** ◇ₖA; k is the grade *)

(** Formula size, used as the outer induction measure in cut admissibility.
    Grades are not counted. *)
Fixpoint size (A : form) : nat :=
  match A with
  | Atom _ => 1
  | One => 1
  | Tensor A B => S (size A + size B)
  | Lolli A B => S (size A + size B)
  | Plus A B => S (size A + size B)
  | Dia _ A => S (size A)
  end.
