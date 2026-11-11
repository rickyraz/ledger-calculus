(** * Candidate B: a uniform cancel on every future

    The v1 system with its [cancel] rule replaced by

<<
     ◇ⱼ(A ⊕ 1), Δ ⊢ C      j ≤ k
    ───────────────────────────── cancel_any
          ◇ₖA, Δ ⊢ C
>>

    Unlike candidate A, this cancel fires on every future, so a cancel on a
    composed future can be pushed back to the future it waits for. Result:
    cut is still NOT admissible ([cut_fails]). The sequent

<<
    ◇₁b,  c   ⊢   ◇₀((b ⊗ c) ⊕ 1)
>>

    follows by cut from [S_left] and [S_right], but has no cut-free
    derivation ([S_not_derivable]).

    Reason: to finish at grade 0 the future ◇₁b must be cancelled first, so
    its content becomes b ⊕ 1. In the branch 1 (cancelled) the resource c is
    still in the context and nothing can consume it: the logic is linear and
    has no weakening. A composable cancel needs the rest of the context to
    be discardable (affine). *)

From Stdlib Require Import List Permutation Lia Arith.
Import ListNotations.

(** ** Syntax and rules (v1 with a different cancel) *)

Inductive form : Type :=
| Atom   : nat -> form
| One    : form
| Tensor : form -> form -> form
| Lolli  : form -> form -> form
| Plus   : form -> form -> form
| Dia    : nat -> form -> form.

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
| cancel_any : forall D k j A C,
    j <= k ->
    seq (Dia j (Plus A One) :: D) C ->
    seq (Dia k A :: D) C.

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
Arguments cancel_any {D k} j {A C}.

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
  - pose proof (await k (submit 0 IHA)) as H.
    rewrite Nat.add_0_r in H. exact H.
Qed.

(** ** The counterexample formulas *)

Notation pB := (Atom 0).
Notation pC := (Atom 1).
Notation fBC := (Tensor pB pC).
Notation fBC1 := (Plus fBC One).
Notation fGoal := (Dia 0 fBC1).

(** ** The invariant: a counting argument

    Contexts are restricted to a small class closed under the premises of
    every rule: the atom c, the unit, "chains" b, b ⊕ 1, (b ⊕ 1) ⊕ 1, ...,
    and futures over chains. We count
    - [is_c]: occurrences of c (each must be consumed exactly once);
    - [is_sure]: formulas that certainly deliver a b at grade 0, namely b
      itself and ◇₀b. A cancelled future ◇ⱼ(chain ⊕ 1) is not sure. *)

Inductive chain : form -> Prop :=
| chain_b : chain pB
| chain_s : forall B, chain B -> chain (Plus B One).

Definition inK (A : form) : Prop :=
  A = pC \/ A = One \/ chain A \/ exists k B, A = Dia k B /\ chain B.

Definition is_c (A : form) : bool :=
  match A with
  | Atom 1 => true
  | _ => false
  end.

Definition is_sure (A : form) : bool :=
  match A with
  | Atom 0 => true
  | Dia 0 (Atom 0) => true
  | _ => false
  end.

Fixpoint cnt (f : form -> bool) (G : list form) : nat :=
  match G with
  | [] => 0
  | A :: G' => (if f A then 1 else 0) + cnt f G'
  end.

Lemma cnt_cons : forall f A G, cnt f (A :: G) = (if f A then 1 else 0) + cnt f G.
Proof. reflexivity. Qed.

Lemma cnt_app : forall f G1 G2, cnt f (G1 ++ G2) = cnt f G1 + cnt f G2.
Proof. induction G1; intros; simpl; [reflexivity | rewrite IHG1; lia]. Qed.

Lemma cnt_perm : forall f G G', Permutation G G' -> cnt f G = cnt f G'.
Proof. induction 1; simpl; lia. Qed.

Lemma Forall_perm : forall (P : form -> Prop) l l',
  Permutation l l' -> Forall P l -> Forall P l'.
Proof.
  intros P l l' Hp H. rewrite Forall_forall in *. intros x Hx.
  apply H. exact (Permutation_in x (Permutation_sym Hp) Hx).
Qed.

Lemma chain_not_c : forall B, chain B -> is_c B = false.
Proof. destruct 1; reflexivity. Qed.

Lemma chain_sure : forall B, chain B -> is_sure (Dia 0 B) = is_sure B.
Proof. destruct 1; reflexivity. Qed.

Lemma cnt_c_dia : forall k B G, cnt is_c (Dia k B :: G) = cnt is_c G.
Proof. reflexivity. Qed.

Lemma cnt_sure_cancelled : forall j B G,
  cnt is_sure (Dia j (Plus B One) :: G) = cnt is_sure G.
Proof. intros j B G. destruct j; reflexivity. Qed.

Lemma cnt_sure_le : forall A G, cnt is_sure G <= cnt is_sure (A :: G).
Proof. intros A G. rewrite cnt_cons. destruct (is_sure A); lia. Qed.

(** What a derivable sequent with goal [C] says about the two counts
    [n] (number of c) and [s] (number of sure b). *)
Definition inv (C : form) (n s : nat) : Prop :=
  (C = pB -> n = 0 /\ 1 <= s) /\
  (C = pC -> n <= 1) /\
  (C = One -> n = 0) /\
  (C = fBC -> n <= s) /\
  (C = fBC1 -> n <= s) /\
  (C = fGoal -> n <= s).

Ltac inv_split :=
  unfold inv;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
  (let e := fresh "e" in intro e; try discriminate e).

Lemma inv_mono : forall C n s s', inv C n s -> s <= s' -> inv C n s'.
Proof.
  unfold inv. intros C n s s' (I1 & I2 & I3 & I4 & I5 & I6) Hle.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); intro e.
  - destruct (I1 e) as [h1 h2]. split; [exact h1 | lia].
  - exact (I2 e).
  - exact (I3 e).
  - specialize (I4 e). lia.
  - specialize (I5 e). lia.
  - specialize (I6 e). lia.
Qed.

Lemma key : forall G C, seq G C ->
  Forall inK G -> inv C (cnt is_c G) (cnt is_sure G).
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
    | G k j A0 C0 Hjk E' IHE ];
    intros HG.
  - (* id_atom *)
    inv_split; injection e as ->; simpl; lia.
  - (* exchange *)
    rewrite <- (cnt_perm is_c _ _ Hp), <- (cnt_perm is_sure _ _ Hp).
    exact (IHE (Forall_perm _ _ _ (Permutation_sym Hp) HG)).
  - (* one_R *)
    inv_split; simpl; lia.
  - (* one_L *)
    apply Forall_cons_iff in HG as [_ HG]. exact (IHE HG).
  - (* tensor_R: only b ⊗ c matters; b needs a sure b, c brings at most one c *)
    apply Forall_app in HG as [Ha Hb].
    destruct (IHa Ha) as (I1 & _). destruct (IHb Hb) as (_ & I2 & _).
    inv_split. injection e as -> ->.
    specialize (I1 eq_refl). specialize (I2 eq_refl).
    rewrite !cnt_app. lia.
  - (* tensor_L: no tensor in the class *)
    apply Forall_cons_iff in HG as [Hh _]. exfalso.
    destruct Hh as [e | [e | [h | (k & B & e & _)]]]; try discriminate e.
    inversion h.
  - (* lolli_R *)
    inv_split.
  - (* lolli_L: no lolli in the class *)
    apply Forall_cons_iff in HG as [Hh _]. exfalso.
    destruct Hh as [e | [e | [h | (k & B & e & _)]]]; try discriminate e.
    inversion h.
  - (* plus_R1 *)
    destruct (IHE HG) as (_ & _ & _ & I4 & _).
    inv_split. injection e as -> ->. exact (I4 eq_refl).
  - (* plus_R2: choosing "cancelled" requires that no c is left *)
    destruct (IHE HG) as (_ & _ & I3 & _).
    inv_split. injection e as -> ->. specialize (I3 eq_refl). lia.
  - (* plus_L on a chain: the branch 1 has the same counts *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [e | [e | [h | (k & B & e & _)]]]; try discriminate e.
    inversion h; subst.
    exact (IH2 (Forall_cons One (or_intror (or_introl eq_refl) : inK One) HG)).
  - (* submit *)
    destruct (IHE HG) as (_ & _ & _ & _ & I5 & _).
    inv_split. injection e as -> ->. exact (I5 eq_refl).
  - (* await: the goal has grade 0, so the future has grade 0 *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [e | [e | [h | (k' & B & e & hB)]]]; try discriminate e;
      [inversion h |].
    injection e as -> ->.
    assert (HK : inK B) by (right; right; left; exact hB).
    destruct (IHE (Forall_cons B HK HG)) as (_ & _ & _ & _ & _ & I6).
    inv_split. injection e as e1 ->.
    assert (k' = 0) by lia. assert (j = 0) by lia. subst.
    specialize (I6 eq_refl).
    rewrite !cnt_cons in I6. rewrite (chain_not_c _ hB) in I6.
    rewrite cnt_c_dia, cnt_cons, (chain_sure _ hB).
    destruct (is_sure B); simpl in *; lia.
  - (* cancel_any: the cancelled future is no longer sure *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [e | [e | [h | (k' & B & e & hB)]]]; try discriminate e;
      [inversion h |].
    injection e as -> ->.
    assert (HK : inK (Dia j (Plus B One))).
    { right; right; right. exists j, (Plus B One).
      split; [reflexivity | exact (chain_s _ hB)]. }
    pose proof (IHE (Forall_cons _ HK HG)) as H.
    rewrite cnt_c_dia, cnt_sure_cancelled in H.
    rewrite cnt_c_dia.
    exact (inv_mono _ _ _ _ H (cnt_sure_le _ _)).
Qed.

(** ** The counterexample *)

Definition S_ctx : list form := [Dia 1 pB; pC].

(** Left premise of the cut: await b, pair it with c, wrap. *)
Lemma S_left : seq S_ctx (Dia 1 fBC).
Proof.
  exact (await (D := [pC]) 1 (j := 0)
           (submit 0 (tensor_R (D1 := [pB]) (D2 := [pC]) (id_atom 0) (id_atom 1)))).
Qed.

(** Right premise of the cut: one [cancel_any] over identity. *)
Lemma S_right : seq [Dia 1 fBC] fGoal.
Proof.
  apply (cancel_any 0); [lia |].
  exact (identity (Dia 0 fBC1)).
Qed.

(** No cut-free derivation: one c in the context, no sure b. *)
Lemma S_not_derivable : ~ seq S_ctx fGoal.
Proof.
  intro E.
  assert (HG : Forall inK S_ctx).
  { apply Forall_cons.
    - right; right; right. exists 1, pB. split; [reflexivity | exact chain_b].
    - apply Forall_cons; [left; reflexivity | apply Forall_nil]. }
  destruct (key _ _ E HG) as (_ & _ & _ & _ & _ & I6).
  specialize (I6 eq_refl). cbv in I6. lia.
Qed.

Theorem cut_fails :
  ~ (forall D1 D2 A C, seq D1 A -> seq (A :: D2) C -> seq (D1 ++ D2) C).
Proof.
  intro cut. apply S_not_derivable.
  exact (cut S_ctx [] _ _ S_left S_right).
Qed.

Print Assumptions cut_fails.
