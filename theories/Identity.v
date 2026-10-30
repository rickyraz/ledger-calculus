(** * Identity expansion: A ⊢ A untuk setiap formula *)

From Stdlib Require Import List Permutation.
From LedgerCalculus Require Import Syntax Sequent.
Import ListNotations.

(** Kasus ◇ₖ memakai [await], jadi teorema ini untuk [aw = true]. *)
Theorem identity : forall A, seq true [A] A.
Proof.
  induction A as [n | | A IHA B IHB | A IHA B IHB | k A IHA].
  - apply id_atom.
  - apply one_L, one_R.
  - apply tensor_L. exact (tensor_R IHA IHB).
  - apply lolli_R.
    apply (exchange (D := [Lolli A B; A])).
    + apply perm_swap.
    + exact (lolli_L (D2 := []) IHA IHB).
  - apply (submit k). exact (await eq_refl IHA).
Qed.
