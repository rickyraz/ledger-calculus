(** * Examples: corollaries, examples, and sanity check *)

From Stdlib Require Import List Permutation Arith.
From LedgerCalculus Require Import Syntax Sequent Identity CutElim.
Import ListNotations.

(** ** Corollary: ◇ₖA ⊬ A for A without ◇ *)

Fixpoint no_dia (A : form) : Prop :=
  match A with
  | Atom _ => True
  | One => True
  | Tensor A B => no_dia A /\ no_dia B
  | Lolli A B => no_dia A /\ no_dia B
  | Plus A B => no_dia A /\ no_dia B
  | Dia _ _ => False
  end.

(** Formulas allowed in the invariant context: without ◇, or ◇ at the head. *)
Definition top_dia_or_free (A : form) : Prop :=
  no_dia A \/ exists k B, A = Dia k B.

Lemma Forall_perm : forall (P : form -> Prop) l l',
  Permutation l l' -> Forall P l -> Forall P l'.
Proof.
  intros P l l' Hp H. rewrite Forall_forall in *. intros x Hx.
  apply H. exact (Permutation_in x (Permutation_sym Hp) Hx).
Qed.

(** Inversion invariant for the cut-free system: if the goal has no ◇ and
    every context formula has no ◇ or is ◇ at the head, then the context has
    no ◇ at all. Only [submit] and [await] can produce a ◇ goal; and [cancel]
    preserves ◇ at the head, so the induction hypothesis is immediately
    contradictory. *)
Lemma dia_free_inv : forall G C, seq G C ->
  Forall top_dia_or_free G -> no_dia C -> Forall no_dia G.
Proof.
  intros G C E.
  induction E as
    [ n
    | G G' C0 Hp E' IHE
    |
    | G C0 E' IHE
    | Ga Gb X Y Ea IHa Eb IHb
    | G X Y C0 E' IHE
    | G X Y E' IHE
    | Ga Gb X Y C0 Ea IHa Eb IHb
    | G X Y E' IHE
    | G X Y E' IHE
    | G X Y C0 E1 IH1 E2 IH2
    | G k X E' IHE
    | G k j X C0 E' IHE
    | G k Rr Xx C0 E' IHE ];
    intros HG HC.
  - (* id_atom *)
    repeat constructor.
  - (* exchange *)
    apply (Forall_perm _ _ _ Hp).
    exact (IHE (Forall_perm _ _ _ (Permutation_sym Hp) HG) HC).
  - (* one_R *)
    constructor.
  - (* one_L *)
    apply Forall_cons_iff in HG as [_ HG].
    constructor; [exact I | exact (IHE HG HC)].
  - (* tensor_R *)
    destruct HC as [HX HY]. apply Forall_app in HG as [Ha Hb].
    apply Forall_app. split; [exact (IHa Ha HX) | exact (IHb Hb HY)].
  - (* tensor_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    assert (hT : no_dia (Tensor X Y)).
    { destruct Hh as [h | (k & B & e)]; [exact h | discriminate e]. }
    destruct hT as [hX hY].
    pose proof (IHE (Forall_cons _ (or_introl hX) (Forall_cons _ (or_introl hY) HG)) HC)
      as Hr.
    apply Forall_cons_iff in Hr as [_ Hr]. apply Forall_cons_iff in Hr as [_ Hr].
    constructor; [split; assumption | exact Hr].
  - (* lolli_R *)
    destruct HC as [hX hY].
    pose proof (IHE (Forall_cons _ (or_introl hX) HG) hY) as Hr.
    apply Forall_cons_iff in Hr as [_ Hr]. exact Hr.
  - (* lolli_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    assert (hT : no_dia (Lolli X Y)).
    { destruct Hh as [h | (k & B & e)]; [exact h | discriminate e]. }
    destruct hT as [hX hY]. apply Forall_app in HG as [Ha Hb].
    pose proof (IHb (Forall_cons _ (or_introl hY) Hb) HC) as Hr.
    apply Forall_cons_iff in Hr as [_ Hr].
    constructor; [split; assumption |].
    apply Forall_app. split; [exact (IHa Ha hX) | exact Hr].
  - (* plus_R1 *)
    destruct HC as [hX _]. exact (IHE HG hX).
  - (* plus_R2 *)
    destruct HC as [_ hY]. exact (IHE HG hY).
  - (* plus_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    assert (hT : no_dia (Plus X Y)).
    { destruct Hh as [h | (k & B & e)]; [exact h | discriminate e]. }
    destruct hT as [hX hY].
    pose proof (IH1 (Forall_cons _ (or_introl hX) HG) HC) as Hr.
    apply Forall_cons_iff in Hr as [_ Hr].
    constructor; [split; assumption | exact Hr].
  - (* submit: goal ◇ *)
    destruct HC.
  - (* await: goal ◇ *)
    destruct HC.
  - (* cancel: premise context still contains ◇ at the head *)
    apply Forall_cons_iff in HG as [_ HG].
    assert (Hd : top_dia_or_free (Dia k (Tensor Rr (Plus Xx One)))).
    { right. eauto. }
    pose proof (IHE (Forall_cons _ Hd HG) HC) as Hr.
    apply Forall_cons_iff in Hr as [Hr _]. destruct Hr.
Qed.

Theorem dia_not_elim : forall k A, no_dia A -> ~ seq [Dia k A] A.
Proof.
  intros k A HA E.
  assert (Hd : top_dia_or_free (Dia k A)) by (right; eauto).
  pose proof (dia_free_inv _ _ E (Forall_cons _ Hd (Forall_nil _)) HA) as Hr.
  apply Forall_cons_iff in Hr as [Hr _]. destruct Hr.
Qed.

(** ** Why the "without ◇" restriction is necessary: ◇₀(◇ⱼB) ⊢ ◇ⱼB *)

Example dia0_dia : forall j B, seq [Dia 0 (Dia j B)] (Dia j B).
Proof. intros j B. exact (await 0 (identity (Dia j B))). Qed.

(** ** cancel can be derived from submit, await (k and 0), and cut

    ◇ₖ(R ⊗ X) ⊢ ◇ₖ(R ⊗ (X ⊕ 1)) is derived with [await k] over
    [submit 0]; the grade is k + 0 = k. Cutting with the premise [cancel]
    gives the conclusion. This proof does not use the [cancel] constructor. *)

Lemma cancel_admissible : forall k R X D C,
  seq (Dia k (Tensor R (Plus X One)) :: D) C ->
  seq (Dia k (Tensor R X) :: D) C.
Proof.
  intros k R X D C E.
  assert (h : seq [Dia k (Tensor R X)] (Dia k (Tensor R (Plus X One)))).
  { pose proof (await k (submit 0
      (tensor_L (tensor_R (identity R) (plus_R1 One (identity X)))))) as H.
    rewrite Nat.add_0_r in H. exact H. }
  exact (cut [Dia k (Tensor R X)] D _ C h E).
Qed.

(** ** Sanity check (not a result): submit → cancel → await → free

    [buf] is an atom, and [free] is the hypothesis [buf ⊸ 1] in the context.
    The future carries resource [buf] and result [1]. After cancel, the result
    becomes [1 ⊕ 1]. Because await is lax, [free] happens inside the future, so
    the goal is ◇ₖ1. The submit step is connected to the rest with [cut]. *)

Definition buf : form := Atom 0.
Definition free : form := Lolli buf One.

Example sanity_submit_cancel_await_free : forall k : nat,
  seq [buf; free] (Dia k One).
Proof.
  intro k.
  (* submit: buf ⊢ ◇ₖ(buf ⊗ 1) *)
  assert (s_submit : seq [buf] (Dia k (Tensor buf One)))
    by exact (submit k (tensor_R (D1 := [buf]) (D2 := []) (id_atom 0) one_R)).
  (* free: buf, buf ⊸ 1 ⊢ 1 *)
  assert (s_free : seq [buf; free] One).
  { apply (exchange (D := [free; buf])); [apply perm_swap |].
    exact (lolli_L (D1 := [buf]) (D2 := []) (id_atom 0) (one_L one_R)). }
  (* future content after cancel: buf ⊗ (1 ⊕ 1), buf ⊸ 1 ⊢ 1 *)
  assert (s_body : seq [Tensor buf (Plus One One); free] One).
  { apply tensor_L.
    apply (exchange (D := [Plus One One; buf; free])); [apply perm_swap |].
    exact (plus_L (one_L s_free) (one_L s_free)). }
  (* await: ◇ₖ(buf ⊗ (1 ⊕ 1)), buf ⊸ 1 ⊢ ◇ₖ1 *)
  assert (s_await : seq [Dia k (Tensor buf (Plus One One)); free] (Dia k One)).
  { pose proof (await k (submit 0 s_body)) as H.
    rewrite Nat.add_0_r in H. exact H. }
  (* cancel: ◇ₖ(buf ⊗ 1), buf ⊸ 1 ⊢ ◇ₖ1 *)
  assert (s_cancel : seq [Dia k (Tensor buf One); free] (Dia k One))
    by exact (cancel s_await).
  exact (cut [buf] [free] _ _ s_submit s_cancel).
Qed.
