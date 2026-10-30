(** * Identity expansion: A ⊢ A untuk setiap formula *)

From Stdlib Require Import List Permutation Arith.
From LedgerCalculus Require Import Syntax Sequent.
Import ListNotations.

Theorem identity : forall A, seq [A] A.
Proof.
  induction A as [n | | A IHA B IHB | A IHA B IHB | A IHA B IHB | k A IHA].
  - apply id_atom.
  - apply one_L, one_R.
  - apply tensor_L. exact (tensor_R IHA IHB).
  - apply lolli_R.
    apply (exchange (D := [Lolli A B; A])).
    + apply perm_swap.
    + exact (lolli_L (D2 := []) IHA IHB).
  - apply plus_L.
    + exact (plus_R1 B IHA).
    + exact (plus_R2 A IHB).
  - (* await k 0 atas submit 0: ◇ₖA ⊢ ◇₍ₖ₊₀₎A *)
    pose proof (await k (submit 0 IHA)) as H.
    rewrite Nat.add_0_r in H. exact H.
Qed.
