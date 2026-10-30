(** * Examples: sanity check dan korolari *)

From Stdlib Require Import List Permutation.
From LedgerCalculus Require Import Syntax Sequent Identity CutElim.
Import ListNotations.

(** ** Sanity check (bukan hasil): submit → cancel → await → free

    [buf] adalah atom, dan [free] adalah hipotesis [buf ⊸ 1] di konteks.
    Resource diserahkan ([submit]), future di-cancel ([cancel]), resource
    diambil kembali hanya lewat [await], lalu dibebaskan. Langkah submit
    disambung ke sisanya dengan [cut] (teorema di [CutElim.v]). *)

Definition buf : form := Atom 0.
Definition free : form := Lolli buf One.

Example sanity_submit_cancel_await_free : forall k : nat,
  seq true [buf; free] One.
Proof.
  intro k.
  (* submit: buf ⊢ ◇ₖ buf *)
  assert (s_submit : seq true [buf] (Dia k buf)) by exact (submit k (id_atom 0)).
  (* free: buf, buf ⊸ 1 ⊢ 1 *)
  assert (s_free : seq true [buf; free] One).
  { apply (exchange (D := [free; buf])); [apply perm_swap |].
    exact (lolli_L (D1 := [buf]) (D2 := []) (id_atom 0) (one_L one_R)). }
  (* cancel lalu await: ◇ₖ buf, buf ⊸ 1 ⊢ 1 *)
  assert (s_cancel_await : seq true [Dia k buf; free] One)
    by exact (cancel (await eq_refl s_free)).
  exact (cut true [buf] [free] (Dia k buf) One s_submit s_cancel_await).
Qed.

(** ** ◇ₖA ⊢ A bisa diturunkan lewat await

    Ini konsekuensi langsung aturan [await] seperti dirumuskan di proposal
    (await : ◇ₖA ⊸ A). Karena itu pernyataan "◇ₖA ⊢ A tidak bisa diturunkan"
    tidak berlaku untuk logika dengan await; lihat README, bagian Konflik. *)

Example dia_elim_via_await : forall k A, seq true [Dia k A] A.
Proof. intros k A. exact (await eq_refl (identity A)). Qed.

(** ** Korolari: tanpa await, ◇ₖp ⊬ p

    Di fragmen tanpa [await] ([aw = false]), tidak ada aturan yang mengubah
    ◇ₖp menjadi p; khususnya [cancel] tidak pernah menghasilkan p. Bukti lewat
    inversi pada sistem cut-free: tidak ada aturan kanan untuk atom, [id_atom]
    butuh p di konteks, aturan kiri lain butuh formula utama yang bukan ◇, dan
    [cancel] serta [exchange] mempertahankan bentuk sequent. *)

Lemma no_await_inv : forall G C, seq false G C ->
  forall k n, Permutation G [Dia k (Atom n)] -> C = Atom n -> False.
Proof.
  intros G C E.
  induction E as
    [ m
    | G G' C0 Hx E' IHE
    |
    | G C0 E' IHE
    | Ga Gb X Y Ea IHa Eb IHb
    | G X Y C0 E' IHE
    | G X Y E' IHE
    | Ga Gb X Y C0 Ea IHa Eb IHb
    | G k X E' IHE
    | G k X C0 Haw E' IHE
    | G k X C0 E' IHE ];
    intros k0 n0 Hp HC; try discriminate HC.
  - (* id_atom *)
    apply Permutation_length_1 in Hp. discriminate Hp.
  - (* exchange *)
    exact (IHE k0 n0 (Permutation_trans Hx Hp) HC).
  - (* one_L *)
    pose proof (Permutation_in One Hp (in_eq _ _)) as Hin.
    destruct Hin as [Hin | []]. discriminate Hin.
  - (* tensor_L *)
    pose proof (Permutation_in (Tensor X Y) Hp (in_eq _ _)) as Hin.
    destruct Hin as [Hin | []]. discriminate Hin.
  - (* lolli_L *)
    pose proof (Permutation_in (Lolli X Y) Hp (in_eq _ _)) as Hin.
    destruct Hin as [Hin | []]. discriminate Hin.
  - (* await: tidak ada di fragmen ini *)
    discriminate Haw.
  - (* cancel *)
    exact (IHE k0 n0 Hp HC).
Qed.

Corollary dia_atom_not_elim_without_await : forall k n,
  ~ seq false [Dia k (Atom n)] (Atom n).
Proof.
  intros k n E. exact (no_await_inv _ _ E k n (Permutation_refl _) eq_refl).
Qed.

(** Dengan [cut_admissible] untuk [aw = false], korolari ini juga berlaku
    untuk fragmen tanpa await yang diberi aturan cut: menambah cut tidak
    menambah sequent yang bisa diturunkan. *)
