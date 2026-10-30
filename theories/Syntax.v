(** * Syntax: formula fragmen (1, ⊗, ⊸, ◇ₖ) *)

Inductive form : Type :=
| Atom   : nat -> form
| One    : form
| Tensor : form -> form -> form
| Lolli  : form -> form -> form
| Dia    : nat -> form -> form.   (** ◇ₖA; grade k belum punya isi semantik *)

(** Ukuran formula, dipakai sebagai ukuran induksi luar di cut admissibility. *)
Fixpoint size (A : form) : nat :=
  match A with
  | Atom _ => 1
  | One => 1
  | Tensor A B => S (size A + size B)
  | Lolli A B => S (size A + size B)
  | Dia _ A => S (size A)
  end.
