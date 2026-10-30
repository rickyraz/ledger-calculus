(** * Cut-free sequent calculus

    One constructor per rule in [docs/rules.md], with the same name. *)

From Stdlib Require Import List Permutation.
From LedgerCalculus Require Import Syntax.
Import ListNotations.

Inductive seq : list form -> form -> Prop :=
| id_atom : forall n,
    seq [Atom n] (Atom n)
| exchange : forall D D' C,
    Permutation D D' -> seq D C -> seq D' C
| one_R :
    seq [] One
| one_L : forall D C,
    seq D C -> seq (One :: D) C
| tensor_R : forall D1 D2 A B,
    seq D1 A -> seq D2 B -> seq (D1 ++ D2) (Tensor A B)
| tensor_L : forall D A B C,
    seq (A :: B :: D) C -> seq (Tensor A B :: D) C
| lolli_R : forall D A B,
    seq (A :: D) B -> seq D (Lolli A B)
| lolli_L : forall D1 D2 A B C,
    seq D1 A -> seq (B :: D2) C -> seq (Lolli A B :: D1 ++ D2) C
| plus_R1 : forall D A B,
    seq D A -> seq D (Plus A B)
| plus_R2 : forall D A B,
    seq D B -> seq D (Plus A B)
| plus_L : forall D A B C,
    seq (A :: D) C -> seq (B :: D) C -> seq (Plus A B :: D) C
| submit : forall D k A,
    seq D A -> seq D (Dia k A)
| await : forall D k j A C,
    seq (A :: D) (Dia j C) -> seq (Dia k A :: D) (Dia (k + j) C)
| cancel : forall D k R X C,
    seq (Dia k (Tensor R (Plus X One)) :: D) C ->
    seq (Dia k (Tensor R X) :: D) C.

Arguments exchange {D D' C}.
Arguments one_L {D C}.
Arguments tensor_R {D1 D2 A B}.
Arguments tensor_L {D A B C}.
Arguments lolli_R {D A B}.
Arguments lolli_L {D1 D2 A B C}.
Arguments plus_R1 {D A} B.
Arguments plus_R2 {D} A {B}.
Arguments plus_L {D A B C}.
Arguments submit {D} k {A}.
Arguments await {D} k {j A C}.
Arguments cancel {D k R X C}.
