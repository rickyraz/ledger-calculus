(** * Candidate A: a cancel that lowers the grade of ◇ₖ(R ⊗ X)

    The v1 system with its [cancel] rule replaced by

<<
     ◇ⱼ(R ⊗ (X ⊕ 1)), Δ ⊢ C      j ≤ k
    ──────────────────────────────────── cancel_down
          ◇ₖ(R ⊗ X), Δ ⊢ C
>>

    Result: cut is NOT admissible ([cut_fails]). The sequent

<<
    ◇₁b,  b ⊸ (r ⊗ x)   ⊢   ◇₀(r ⊗ (x ⊕ 1))
>>

    follows from two cut-free derivable sequents by cut ([S_left],
    [S_right]) but has no cut-free derivation ([S_not_derivable]).

    The non-derivability proof is an invariant ([grade_lower_bound]): when
    every future in the context wraps an atom, the grade of the goal is at
    least the sum of the grades in the context. [cancel_down] cannot fire on
    such a future, so nothing can lower the grade. *)

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
| cancel_down : forall D k j R X C,
    j <= k ->
    seq (Dia j (Tensor R (Plus X One)) :: D) C ->
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
Arguments cancel_down {D k} j {R X C}.

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

(** ** The invariant: grades in the context are a lower bound *)

Fixpoint no_dia (A : form) : Prop :=
  match A with
  | Atom _ => True
  | One => True
  | Tensor A B => no_dia A /\ no_dia B
  | Lolli A B => no_dia A /\ no_dia B
  | Plus A B => no_dia A /\ no_dia B
  | Dia _ _ => False
  end.

Definition grade (A : form) : nat :=
  match A with
  | Dia k _ => k
  | _ => 0
  end.

Fixpoint gsum (G : list form) : nat :=
  match G with
  | [] => 0
  | A :: G' => grade A + gsum G'
  end.

Lemma gsum_app : forall G1 G2, gsum (G1 ++ G2) = gsum G1 + gsum G2.
Proof. induction G1; intros; simpl; [reflexivity | rewrite IHG1; lia]. Qed.

Lemma gsum_perm : forall G G', Permutation G G' -> gsum G = gsum G'.
Proof. induction 1; simpl; lia. Qed.

Lemma no_dia_grade : forall A, no_dia A -> grade A = 0.
Proof. destruct A; simpl; intro h; try reflexivity. destruct h. Qed.

Lemma Forall_perm : forall (P : form -> Prop) l l',
  Permutation l l' -> Forall P l -> Forall P l'.
Proof.
  intros P l l' Hp H. rewrite Forall_forall in *. intros x Hx.
  apply H. exact (Permutation_in x (Permutation_sym Hp) Hx).
Qed.

(** Context formulas allowed by the invariant: no ◇ at all, or a future that
    wraps an atom. Goals allowed: no ◇ at all, or one ◇ at the head. *)
Definition ctx_ok (A : form) : Prop :=
  no_dia A \/ exists k n, A = Dia k (Atom n).

Definition goal_ok (C : form) : Prop :=
  no_dia C \/ exists j C', C = Dia j C' /\ no_dia C'.

Lemma grade_lower_bound : forall G C, seq G C ->
  Forall ctx_ok G -> goal_ok C -> gsum G <= grade C.
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
    | G k j Rr Xx C0 Hjk E' IHE ];
    intros HG HC.
  - (* id_atom *)
    simpl. lia.
  - (* exchange *)
    rewrite <- (gsum_perm _ _ Hp).
    exact (IHE (Forall_perm _ _ _ (Permutation_sym Hp) HG) HC).
  - (* one_R *)
    simpl. lia.
  - (* one_L *)
    apply Forall_cons_iff in HG as [_ HG]. exact (IHE HG HC).
  - (* tensor_R *)
    apply Forall_app in HG as [Ha Hb].
    destruct HC as [[hX hY] | (j & C' & e & _)]; [| discriminate e].
    pose proof (IHa Ha (or_introl hX)) as H1.
    pose proof (IHb Hb (or_introl hY)) as H2.
    pose proof (no_dia_grade _ hX) as eX. pose proof (no_dia_grade _ hY) as eY.
    rewrite gsum_app. simpl. lia.
  - (* tensor_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [[hX hY] | (k & n & e)]; [| discriminate e].
    pose proof (IHE (Forall_cons _ (or_introl hX) (Forall_cons _ (or_introl hY) HG)) HC) as H.
    pose proof (no_dia_grade _ hX) as eX. pose proof (no_dia_grade _ hY) as eY.
    simpl in *. lia.
  - (* lolli_R *)
    destruct HC as [[hX hY] | (j & C' & e & _)]; [| discriminate e].
    pose proof (IHE (Forall_cons _ (or_introl hX) HG) (or_introl hY)) as H.
    pose proof (no_dia_grade _ hX) as eX. pose proof (no_dia_grade _ hY) as eY.
    simpl in *. lia.
  - (* lolli_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [[hX hY] | (k & n & e)]; [| discriminate e].
    apply Forall_app in HG as [Ha Hb].
    pose proof (IHa Ha (or_introl hX)) as H1.
    pose proof (IHb (Forall_cons _ (or_introl hY) Hb) HC) as H2.
    pose proof (no_dia_grade _ hX) as eX. pose proof (no_dia_grade _ hY) as eY.
    simpl in *. rewrite gsum_app. lia.
  - (* plus_R1 *)
    destruct HC as [[hX hY] | (j & C' & e & _)]; [| discriminate e].
    pose proof (IHE HG (or_introl hX)) as H.
    pose proof (no_dia_grade _ hX) as eX. simpl. lia.
  - (* plus_R2 *)
    destruct HC as [[hX hY] | (j & C' & e & _)]; [| discriminate e].
    pose proof (IHE HG (or_introl hY)) as H.
    pose proof (no_dia_grade _ hY) as eY. simpl. lia.
  - (* plus_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [[hX hY] | (k & n & e)]; [| discriminate e].
    pose proof (IH1 (Forall_cons _ (or_introl hX) HG) HC) as H.
    pose proof (no_dia_grade _ hX) as eX. simpl in *. lia.
  - (* submit: the content has no ◇, so the context has grade sum 0 *)
    destruct HC as [h | (j & C' & e & hC)]; [destruct h |].
    injection e as -> ->.
    pose proof (IHE HG (or_introl hC)) as H.
    pose proof (no_dia_grade _ hC) as eC. simpl. lia.
  - (* await: adds k on both sides *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [h | (k' & n & e)]; [destruct h |].
    injection e as -> ->.
    destruct HC as [h | (j' & C' & e & hC)]; [destruct h |].
    injection e as e1 ->.
    assert (Hg : goal_ok (Dia j C'))
      by (right; exists j, C'; split; [reflexivity | exact hC]).
    pose proof (IHE (Forall_cons (Atom n) (or_introl I : ctx_ok (Atom n)) HG) Hg) as H.
    simpl in *. lia.
  - (* cancel_down: cannot fire, the future wraps an atom *)
    apply Forall_cons_iff in HG as [Hh _].
    destruct Hh as [h | (k' & n & e)]; [destruct h | discriminate e].
Qed.

(** ** The counterexample *)

Definition b : form := Atom 0.
Definition r : form := Atom 1.
Definition x : form := Atom 2.

Definition S_ctx : list form := [Dia 1 b; Lolli b (Tensor r x)].
Definition S_goal : form := Dia 0 (Tensor r (Plus x One)).

(** Left premise of the cut: await b, call the function, wrap. *)
Lemma S_left : seq S_ctx (Dia 1 (Tensor r x)).
Proof.
  assert (h : seq [b; Lolli b (Tensor r x)] (Tensor r x)).
  { apply (exchange (D := [Lolli b (Tensor r x); b])); [apply perm_swap |].
    exact (lolli_L (D1 := [b]) (D2 := []) (id_atom 0) (identity (Tensor r x))). }
  exact (await (D := [Lolli b (Tensor r x)]) 1 (j := 0) (submit 0 h)).
Qed.

(** Right premise of the cut: one [cancel_down] over identity. *)
Lemma S_right : seq [Dia 1 (Tensor r x)] S_goal.
Proof.
  apply (cancel_down 0); [lia |].
  exact (identity (Dia 0 (Tensor r (Plus x One)))).
Qed.

(** No cut-free derivation: context grade sum is 1, goal grade is 0. *)
Lemma S_not_derivable : ~ seq S_ctx S_goal.
Proof.
  intro E.
  assert (HG : Forall ctx_ok S_ctx).
  { apply Forall_cons; [right; exists 1, 0; reflexivity |].
    apply Forall_cons; [left; cbv; tauto | apply Forall_nil]. }
  assert (HC : goal_ok S_goal).
  { right. exists 0, (Tensor r (Plus x One)). split; [reflexivity | cbv; tauto]. }
  pose proof (grade_lower_bound _ _ E HG HC) as H.
  cbv in H. lia.
Qed.

Theorem cut_fails :
  ~ (forall D1 D2 A C, seq D1 A -> seq (A :: D2) C -> seq (D1 ++ D2) C).
Proof.
  intro cut. apply S_not_derivable.
  exact (cut S_ctx [] _ _ S_left S_right).
Qed.

Print Assumptions cut_fails.
