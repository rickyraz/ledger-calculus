(** * Sequent calculus cut-free

    Satu konstruktor per aturan di [docs/rules.md], dengan nama yang sama.
    Parameter [aw] memilih fragmen: [await] hanya berlaku bila [aw = true]. *)

From Stdlib Require Import List Permutation.
From LedgerCalculus Require Import Syntax.
Import ListNotations.

Inductive seq (aw : bool) : list form -> form -> Prop :=
| id_atom : forall n,
    seq aw [Atom n] (Atom n)
| exchange : forall D D' C,
    Permutation D D' -> seq aw D C -> seq aw D' C
| one_R :
    seq aw [] One
| one_L : forall D C,
    seq aw D C -> seq aw (One :: D) C
| tensor_R : forall D1 D2 A B,
    seq aw D1 A -> seq aw D2 B -> seq aw (D1 ++ D2) (Tensor A B)
| tensor_L : forall D A B C,
    seq aw (A :: B :: D) C -> seq aw (Tensor A B :: D) C
| lolli_R : forall D A B,
    seq aw (A :: D) B -> seq aw D (Lolli A B)
| lolli_L : forall D1 D2 A B C,
    seq aw D1 A -> seq aw (B :: D2) C -> seq aw (Lolli A B :: D1 ++ D2) C
| submit : forall D k A,
    seq aw D A -> seq aw D (Dia k A)
| await : forall D k A C,
    aw = true -> seq aw (A :: D) C -> seq aw (Dia k A :: D) C
| cancel : forall D k A C,
    seq aw (Dia k A :: D) C -> seq aw (Dia k A :: D) C.

Arguments id_atom {aw}.
Arguments exchange {aw D D' C}.
Arguments one_R {aw}.
Arguments one_L {aw D C}.
Arguments tensor_R {aw D1 D2 A B}.
Arguments tensor_L {aw D A B C}.
Arguments lolli_R {aw D A B}.
Arguments lolli_L {aw D1 D2 A B C}.
Arguments submit {aw D} k {A}.
Arguments await {aw D k A C}.
Arguments cancel {aw D k A C}.
