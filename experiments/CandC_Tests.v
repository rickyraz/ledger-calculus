(** * Candidate C: tests

    The specification is the list of negative tests in chapter 11 of the
    notes ("must NOT be derivable" 1-5, "must be derivable" 6-7, and "the
    protocol cannot be skipped").

    Notation: [seq sp cn]. Unless stated otherwise the tests are about the
    token variant, [sp = false]: tokens cannot be built by user code.

    | Test                                              | Lemma |
    |---------------------------------------------------|-------|
    | 1. no in-flight token without a submit operation  | [no_fake_token], [t1_no_fake_inflight] |
    | 2. no cancelled status without cancel             | [no_cnc_without_cancel], [t2_no_cnc_without_cancel] |
    | 3. cancel cannot be used twice                    | [cnc_rigid], [t3_no_second_speedup] |
    | 4. R cannot leave an in-flight operation          | [tok_not_elim], [t4_no_free_in_flight], [t4_no_free_after_cancel_request] |
    | 5. cancel is not derivable from the other rules   | [t5_cancel_needed], [t5_after_cancel] |
    | 6. normal path                                    | [t6_path_normal] |
    | 7. cancel path                                    | [t7_path_cancel] |
    | 8. the cancel path needs cancel                   | [t8_no_shortcut], [t8_normal_not_faster] |

    For contrast, with [sp = true] tests 1 and 2 fail:
    [spawn_fake_inflight], [spawn_fake_cancelled]. *)

From Stdlib Require Import List Permutation Lia Arith.
From LedgerExp Require Import CandC.
Import ListNotations.

Lemma Forall_perm : forall (P : form -> Prop) l l',
  Permutation l l' -> Forall P l -> Forall P l'.
Proof.
  intros P l l' Hp H. rewrite Forall_forall in *. intros x Hx.
  apply H. exact (Permutation_in x (Permutation_sym Hp) Hx).
Qed.

(** ** Test 4: nothing leaves a token or a future without an await

    [nomod A]: A contains neither ◇ nor a token. Generalises [dia_free_inv]
    of v1: if the goal has no modality and every context formula is either
    modality-free or a future/token at the head, then the context has no
    future/token at all. *)

Fixpoint nomod (A : form) : Prop :=
  match A with
  | Atom _ => True
  | One => True
  | Tensor A B => nomod A /\ nomod B
  | Lolli A B => nomod A /\ nomod B
  | Plus A B => nomod A /\ nomod B
  | Dia _ _ => False
  | Tok _ _ _ _ => False
  end.

Definition top_or_free (A : form) : Prop :=
  nomod A \/ (exists k B, A = Dia k B) \/ (exists s k R X, A = Tok s k R X).

Lemma top_or_free_nomod_tensor : forall X Y, top_or_free (Tensor X Y) -> nomod (Tensor X Y).
Proof.
  intros X Y [h | [(k & B & e) | (s & k & R & X0 & e)]];
    [exact h | discriminate e | discriminate e].
Qed.

Lemma top_or_free_nomod_lolli : forall X Y, top_or_free (Lolli X Y) -> nomod (Lolli X Y).
Proof.
  intros X Y [h | [(k & B & e) | (s & k & R & X0 & e)]];
    [exact h | discriminate e | discriminate e].
Qed.

Lemma top_or_free_nomod_plus : forall X Y, top_or_free (Plus X Y) -> nomod (Plus X Y).
Proof.
  intros X Y [h | [(k & B & e) | (s & k & R & X0 & e)]];
    [exact h | discriminate e | discriminate e].
Qed.

Lemma modal_free_inv : forall sp cn G C, seq sp cn G C ->
  Forall top_or_free G -> nomod C -> Forall nomod G.
Proof.
  intros sp cn G C E.
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
    | s k Rr Xx
    | G s k j Rr Xx C0 E' IHE
    | G k j Rr Xx C0 Hcn Hjk E' IHE
    | Ga Gb s k Rr Xx Hsp Ea IHa Eb IHb ];
    intros HG HC.
  - (* id_atom *)
    apply Forall_cons; [exact I | apply Forall_nil].
  - (* exchange *)
    apply (Forall_perm _ _ _ Hp).
    exact (IHE (Forall_perm _ _ _ (Permutation_sym Hp) HG) HC).
  - (* one_R *)
    apply Forall_nil.
  - (* one_L *)
    apply Forall_cons_iff in HG as [_ HG].
    apply Forall_cons; [exact I | exact (IHE HG HC)].
  - (* tensor_R *)
    destruct HC as [HX HY]. apply Forall_app in HG as [Ha Hb].
    apply Forall_app. split; [exact (IHa Ha HX) | exact (IHb Hb HY)].
  - (* tensor_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    pose proof (top_or_free_nomod_tensor _ _ Hh) as hT.
    destruct hT as [hX hY].
    pose proof (IHE (Forall_cons X (or_introl hX : top_or_free X)
                       (Forall_cons Y (or_introl hY : top_or_free Y) HG)) HC) as Hr.
    apply Forall_cons_iff in Hr as [_ Hr]. apply Forall_cons_iff in Hr as [_ Hr].
    apply Forall_cons; [split; assumption | exact Hr].
  - (* lolli_R *)
    destruct HC as [hX hY].
    pose proof (IHE (Forall_cons X (or_introl hX : top_or_free X) HG) hY) as Hr.
    apply Forall_cons_iff in Hr as [_ Hr]. exact Hr.
  - (* lolli_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    pose proof (top_or_free_nomod_lolli _ _ Hh) as hT.
    destruct hT as [hX hY]. apply Forall_app in HG as [Ha Hb].
    pose proof (IHb (Forall_cons Y (or_introl hY : top_or_free Y) Hb) HC) as Hr.
    apply Forall_cons_iff in Hr as [_ Hr].
    apply Forall_cons; [split; assumption |].
    apply Forall_app. split; [exact (IHa Ha hX) | exact Hr].
  - (* plus_R1 *)
    destruct HC as [hX _]. exact (IHE HG hX).
  - (* plus_R2 *)
    destruct HC as [_ hY]. exact (IHE HG hY).
  - (* plus_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    pose proof (top_or_free_nomod_plus _ _ Hh) as hT.
    destruct hT as [hX hY].
    pose proof (IH1 (Forall_cons X (or_introl hX : top_or_free X) HG) HC) as Hr.
    apply Forall_cons_iff in Hr as [_ Hr].
    apply Forall_cons; [split; assumption | exact Hr].
  - (* ret: goal ◇ *)
    destruct HC.
  - (* await: goal ◇ *)
    destruct HC.
  - (* tok_id: goal is a token *)
    destruct HC.
  - (* tok_await: goal ◇ *)
    destruct HC.
  - (* tok_cancel: the premise still has a token at the head *)
    apply Forall_cons_iff in HG as [_ HG].
    assert (Hd : top_or_free (Tok Cnc j Rr Xx))
      by (right; right; exists Cnc, j, Rr, Xx; reflexivity).
    pose proof (IHE (Forall_cons _ Hd HG) HC) as Hr.
    apply Forall_cons_iff in Hr as [Hr _]. destruct Hr.
  - (* spawn: goal is a token *)
    destruct HC.
Qed.

(** Test 4. An in-flight (or cancelling) operation alone never yields a
    modality-free formula: neither R, nor X, nor anything built from them.
    Holds for every setting of the switches. *)
Theorem tok_not_elim : forall sp cn s k R X C,
  nomod C -> ~ seq sp cn [Tok s k R X] C.
Proof.
  intros sp cn s k R X C HC E.
  assert (Hd : top_or_free (Tok s k R X))
    by (right; right; exists s, k, R, X; reflexivity).
  pose proof (modal_free_inv _ _ _ _ E (Forall_cons _ Hd (Forall_nil _)) HC) as Hr.
  apply Forall_cons_iff in Hr as [Hr _]. destruct Hr.
Qed.

(** The v1 result still holds. *)
Theorem dia_not_elim : forall sp cn k A, nomod A -> ~ seq sp cn [Dia k A] A.
Proof.
  intros sp cn k A HA E.
  assert (Hd : top_or_free (Dia k A)) by (right; left; exists k, A; reflexivity).
  pose proof (modal_free_inv _ _ _ _ E (Forall_cons _ Hd (Forall_nil _)) HA) as Hr.
  apply Forall_cons_iff in Hr as [Hr _]. destruct Hr.
Qed.

(** ** Tests 1 and 2: tokens cannot be forged

    [clean f A]: A contains no token whose status satisfies [f]. Without
    [spawn], a goal token of a forbidden status can only come from a context
    that already contains one. *)

Fixpoint clean (f : st -> bool) (A : form) : Prop :=
  match A with
  | Atom _ => True
  | One => True
  | Tensor A B => clean f A /\ clean f B
  | Lolli A B => clean f A /\ clean f B
  | Plus A B => clean f A /\ clean f B
  | Dia _ A => clean f A
  | Tok s _ R X => f s = false /\ clean f R /\ clean f X
  end.

Lemma no_forgery : forall cn f G C, seq false cn G C ->
  (cn = true -> f Fly = true) ->
  Forall (clean f) G ->
  forall s k R X, C = Tok s k R X -> f s = true -> False.
Proof.
  intros cn f G C E Hf.
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
    | s k Rr Xx
    | G s k j Rr Xx C0 E' IHE
    | G k j Rr Xx C0 Hcn Hjk E' IHE
    | Ga Gb s k Rr Xx Hsp Ea IHa Eb IHb ];
    intros HG s0 k0 R0 X0 HC Hs; try discriminate HC.
  - (* exchange *)
    exact (IHE (Forall_perm _ _ _ (Permutation_sym Hp) HG) s0 k0 R0 X0 HC Hs).
  - (* one_L *)
    apply Forall_cons_iff in HG as [_ HG].
    exact (IHE HG s0 k0 R0 X0 HC Hs).
  - (* tensor_L *)
    apply Forall_cons_iff in HG as [[hX hY] HG].
    exact (IHE (Forall_cons _ hX (Forall_cons _ hY HG)) s0 k0 R0 X0 HC Hs).
  - (* lolli_L *)
    apply Forall_cons_iff in HG as [[hX hY] HG].
    apply Forall_app in HG as [Ha Hb].
    exact (IHb (Forall_cons _ hY Hb) s0 k0 R0 X0 HC Hs).
  - (* plus_L *)
    apply Forall_cons_iff in HG as [[hX hY] HG].
    exact (IH1 (Forall_cons _ hX HG) s0 k0 R0 X0 HC Hs).
  - (* tok_id: the token was already in the context *)
    injection HC as -> -> -> ->.
    apply Forall_cons_iff in HG as [[h _] _].
    rewrite h in Hs. discriminate Hs.
  - (* tok_cancel: needs a Fly token in the context *)
    apply Forall_cons_iff in HG as [[h _] _].
    rewrite (Hf Hcn) in h. discriminate h.
  - (* spawn: switched off *)
    discriminate Hsp.
Qed.

Definition tokfree : form -> Prop := clean (fun _ => true).

Definition is_cnc (s : st) : bool :=
  match s with
  | Cnc => true
  | Fly => false
  end.

(** Test 1. From a context without tokens, no token can be produced:
    an in-flight operation exists only if some hypothesis (the kernel
    interface) hands it out. *)
Theorem no_fake_token : forall cn G s k R X,
  Forall tokfree G -> ~ seq false cn G (Tok s k R X).
Proof.
  intros cn G s k R X HG E.
  exact (no_forgery cn (fun _ => true) G _ E (fun _ => eq_refl) HG s k R X
           eq_refl eq_refl).
Qed.

(** Test 2. Without the cancel rule, a context without cancelled tokens
    never produces a cancelled token. *)
Theorem no_cnc_without_cancel : forall G k R X,
  Forall (clean is_cnc) G -> ~ seq false false G (Tok Cnc k R X).
Proof.
  intros G k R X HG E.
  refine (no_forgery false is_cnc G _ E _ HG Cnc k R X eq_refl eq_refl).
  intro h. discriminate h.
Qed.

(** ** Test 3 (first half): a cancelled token is rigid

    From a cancelled token alone, the only token one can produce is that
    same token: same status, same grade. There is no second cancel. *)

Lemma cnc_rigid_aux : forall cn G C, seq false cn G C ->
  forall j R X, G = [Tok Cnc j R X] ->
  forall s i R' X', C = Tok s i R' X' ->
  s = Cnc /\ i = j /\ R' = R /\ X' = X.
Proof.
  intros cn G C E.
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
    | s k Rr Xx
    | G s k j Rr Xx C0 E' IHE
    | G k j Rr Xx C0 Hcn Hjk E' IHE
    | Ga Gb s k Rr Xx Hsp Ea IHa Eb IHb ];
    intros j0 R0 X0 HG s0 i0 R1 X1 HC;
    try discriminate HC; try discriminate HG.
  - (* exchange *)
    subst G'. apply Permutation_sym, Permutation_length_1_inv in Hp.
    exact (IHE j0 R0 X0 Hp s0 i0 R1 X1 HC).
  - (* tok_id *)
    injection HG as -> -> -> ->. injection HC as <- <- <- <-.
    repeat split; reflexivity.
  - (* spawn: switched off *)
    discriminate Hsp.
Qed.

Theorem cnc_rigid : forall cn j R X s i R' X',
  seq false cn [Tok Cnc j R X] (Tok s i R' X') ->
  s = Cnc /\ i = j /\ R' = R /\ X' = X.
Proof.
  intros cn j R X s i R' X' E.
  exact (cnc_rigid_aux cn _ _ E j R X eq_refl s i R' X' eq_refl).
Qed.

(** ** Grades are a lower bound (tests 3, 5, 8)

    Each formula in the context has a weight: the time one must wait for it.
    - a future ◇ₖ: k;
    - a cancelled token: its grade (it cannot be cancelled again);
    - an in-flight token: its grade if there is no cancel rule, 0 if there
      is one (it may be cancelled down to 0);
    - a kernel operation [p ⊸ Tok s k ...]: the weight of the token it
      will hand out.
    Claim: the grade of the goal is at least the sum of the weights. *)

Definition tokw (cn : bool) (s : st) (k : nat) : nat :=
  match s with
  | Cnc => k
  | Fly => if cn then 0 else k
  end.

Definition wt (cn : bool) (A : form) : nat :=
  match A with
  | Dia k _ => k
  | Tok s k _ _ => tokw cn s k
  | Lolli _ (Tok s k _ _) => tokw cn s k
  | _ => 0
  end.

Definition grade (C : form) : nat :=
  match C with
  | Dia k _ => k
  | _ => 0
  end.

Fixpoint gsum (cn : bool) (G : list form) : nat :=
  match G with
  | [] => 0
  | A :: G' => wt cn A + gsum cn G'
  end.

Lemma gsum_cons : forall cn A G, gsum cn (A :: G) = wt cn A + gsum cn G.
Proof. reflexivity. Qed.

Lemma gsum_app : forall cn G1 G2, gsum cn (G1 ++ G2) = gsum cn G1 + gsum cn G2.
Proof. induction G1; intros; simpl; [reflexivity | rewrite IHG1; lia]. Qed.

Lemma gsum_perm : forall cn G G', Permutation G G' -> gsum cn G = gsum cn G'.
Proof. induction 1; simpl; lia. Qed.

Lemma nomod_wt : forall cn A, nomod A -> wt cn A = 0.
Proof.
  intros cn A h.
  destruct A as [n | | A B | A B | A B | k A | s k R X]; simpl in *;
    try reflexivity; try (destruct h; fail).
  destruct h as [_ h]. destruct B; simpl in *; try reflexivity. destruct h.
Qed.

Lemma nomod_grade : forall C, nomod C -> grade C = 0.
Proof. destruct C; simpl; intro h; try reflexivity; destruct h. Qed.

Lemma tokw_le : forall cn s k, tokw cn s k <= k.
Proof. intros cn s k. destruct s, cn; simpl; lia. Qed.

Lemma nomod_res_atom : forall s m, nomod (res s (Atom m)).
Proof. intros s m. destruct s; simpl; tauto. Qed.

(** Context formulas covered: modality-free, a future over an atom, a token
    over atoms, or a kernel operation that hands out such a token. *)
Definition ctx_ok (A : form) : Prop :=
  nomod A \/
  (exists k n, A = Dia k (Atom n)) \/
  (exists s k n m, A = Tok s k (Atom n) (Atom m)) \/
  (exists a s k n m, A = Lolli (Atom a) (Tok s k (Atom n) (Atom m))).

Definition goal_ok (C : form) : Prop :=
  nomod C \/ exists j C', C = Dia j C' /\ nomod C'.

Lemma grade_lower_bound : forall cn G C, seq false cn G C ->
  Forall ctx_ok G -> goal_ok C -> gsum cn G <= grade C.
Proof.
  intros cn G C E.
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
    | s k Rr Xx
    | G s k j Rr Xx C0 E' IHE
    | G k j Rr Xx C0 Hcn Hjk E' IHE
    | Ga Gb s k Rr Xx Hsp Ea IHa Eb IHb ];
    intros HG HC.
  - (* id_atom *)
    simpl. lia.
  - (* exchange *)
    rewrite <- (gsum_perm cn _ _ Hp).
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
    pose proof (nomod_grade _ hX) as eX. pose proof (nomod_grade _ hY) as eY.
    rewrite gsum_app. simpl. lia.
  - (* tensor_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [[hX hY] | [(k' & n & e) | [(s' & k' & n & m & e)
                                | (a & s' & k' & n & m & e)]]];
      try discriminate e.
    pose proof (IHE (Forall_cons X (or_introl hX : ctx_ok X)
                       (Forall_cons Y (or_introl hY : ctx_ok Y) HG)) HC) as H.
    pose proof (nomod_wt cn _ hX) as eX. pose proof (nomod_wt cn _ hY) as eY.
    rewrite !gsum_cons in H. rewrite gsum_cons. simpl. lia.
  - (* lolli_R *)
    destruct HC as [[hX hY] | (j & C' & e & _)]; [| discriminate e].
    pose proof (IHE (Forall_cons X (or_introl hX : ctx_ok X) HG) (or_introl hY)) as H.
    pose proof (nomod_wt cn _ hX) as eX. pose proof (nomod_grade _ hY) as eY.
    rewrite gsum_cons in H. simpl. lia.
  - (* lolli_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    apply Forall_app in HG as [Ha Hb].
    destruct Hh as [[hX hY] | [(k' & n & e) | [(s' & k' & n & m & e)
                                | (a & s' & k' & n & m & e)]]];
      try discriminate e.
    + (* an ordinary function *)
      pose proof (IHa Ha (or_introl hX)) as H1.
      pose proof (IHb (Forall_cons Y (or_introl hY : ctx_ok Y) Hb) HC) as H2.
      pose proof (nomod_grade _ hX) as eX. pose proof (nomod_wt cn _ hY) as eY.
      pose proof (nomod_wt cn (Lolli X Y) (conj hX hY)) as eL.
      rewrite gsum_cons in H2. rewrite gsum_cons, gsum_app. lia.
    + (* a kernel operation: its weight is the weight of the token *)
      injection e as -> ->.
      assert (Hk : ctx_ok (Tok s' k' (Atom n) (Atom m)))
        by (right; right; left; exists s', k', n, m; reflexivity).
      pose proof (IHa Ha (or_introl I : goal_ok (Atom a))) as H1.
      pose proof (IHb (Forall_cons _ Hk Hb) HC) as H2.
      rewrite gsum_cons in H2. rewrite gsum_cons, gsum_app.
      simpl in *. lia.
  - (* plus_R1 *)
    destruct HC as [[hX hY] | (j & C' & e & _)]; [| discriminate e].
    pose proof (IHE HG (or_introl hX)) as H.
    pose proof (nomod_grade _ hX) as eX. simpl. lia.
  - (* plus_R2 *)
    destruct HC as [[hX hY] | (j & C' & e & _)]; [| discriminate e].
    pose proof (IHE HG (or_introl hY)) as H.
    pose proof (nomod_grade _ hY) as eY. simpl. lia.
  - (* plus_L *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [[hX hY] | [(k' & n & e) | [(s' & k' & n & m & e)
                                | (a & s' & k' & n & m & e)]]];
      try discriminate e.
    pose proof (IH1 (Forall_cons X (or_introl hX : ctx_ok X) HG) HC) as H.
    pose proof (nomod_wt cn _ hX) as eX.
    rewrite gsum_cons in H. rewrite gsum_cons. simpl. lia.
  - (* ret *)
    destruct HC as [h | (j & C' & e & hC)]; [destruct h |].
    injection e as -> ->.
    pose proof (IHE HG (or_introl hC)) as H.
    pose proof (nomod_grade _ hC) as eC. simpl. lia.
  - (* await *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [h | [(k' & n & e) | [(s' & k' & n & m & e)
                          | (a & s' & k' & n & m & e)]]];
      [destruct h | | discriminate e | discriminate e].
    injection e as -> ->.
    destruct HC as [h | (j' & C' & e & hC)]; [destruct h |].
    injection e as e1 ->.
    assert (Hg : goal_ok (Dia j C'))
      by (right; exists j, C'; split; [reflexivity | exact hC]).
    pose proof (IHE (Forall_cons (Atom n) (or_introl I : ctx_ok (Atom n)) HG) Hg) as H.
    simpl in *. lia.
  - (* tok_id: a token goal is outside the covered goals *)
    destruct HC as [h | (j' & C' & e & _)]; [destruct h | discriminate e].
  - (* tok_await *)
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [h | [(k' & n & e) | [(s' & k' & n & m & e)
                          | (a & s' & k' & n & m & e)]]];
      [destruct h | discriminate e | | discriminate e].
    injection e as -> -> -> ->.
    destruct HC as [h | (j' & C' & e & hC)]; [destruct h |].
    injection e as e1 ->.
    assert (Hg : goal_ok (Dia j C'))
      by (right; exists j, C'; split; [reflexivity | exact hC]).
    pose proof (nomod_res_atom s' m) as hres.
    pose proof (IHE (Forall_cons (Atom n) (or_introl I : ctx_ok (Atom n))
                       (Forall_cons _ (or_introl hres : ctx_ok (res s' (Atom m))) HG))
                    Hg) as H.
    rewrite !gsum_cons in H. rewrite (nomod_wt cn _ hres) in H.
    rewrite gsum_cons.
    pose proof (tokw_le cn s' k') as Hw.
    simpl in *. lia.
  - (* tok_cancel: an in-flight token weighs 0 when cancel exists *)
    subst cn.
    apply Forall_cons_iff in HG as [Hh HG].
    destruct Hh as [h | [(k' & n & e) | [(s' & k' & n & m & e)
                          | (a & s' & k' & n & m & e)]]];
      [destruct h | discriminate e | | discriminate e].
    injection e as <- -> -> ->.
    assert (Hk : ctx_ok (Tok Cnc j (Atom n) (Atom m)))
      by (right; right; left; exists Cnc, j, n, m; reflexivity).
    pose proof (IHE (Forall_cons _ Hk HG) HC) as H.
    simpl in *. lia.
  - (* spawn: switched off *)
    discriminate Hsp.
Qed.

(** ** The io_uring read protocol as a concrete instance *)

Definition buf : form := Atom 0.                          (* the buffer *)
Definition nres : form := Atom 1.                         (* the result: bytes read *)
Definition free : form := Lolli buf One.                  (* free : buf ⊸ 1 *)
Definition inflight : form := Tok Fly 5 buf nres.         (* read in flight, done within 5 *)
Definition read : form := Lolli buf inflight.             (* kernel interface: submit a read *)

(** [free] consumes one [buf]. *)
Lemma use_free : forall sp cn D C,
  seq sp cn D C -> seq sp cn (free :: buf :: D) C.
Proof.
  intros sp cn D C E.
  exact (lolli_L (D1 := [buf]) (D2 := D) (id_atom 0) (one_L E)).
Qed.

(** Test 6. Normal path: submit, await, free. The result arrives at grade 5. *)
Example t6_path_normal : seq false false [buf; read; free] (Dia 5 nres).
Proof.
  apply (exchange (D := [read; buf; free])); [apply perm_swap |].
  apply (lolli_L (D1 := [buf]) (D2 := [free])); [exact (id_atom 0) |].
  (* inflight, free ⊢ ◇₅ nres *)
  apply (tok_await 5 (j := 0)).
  apply ret.
  (* buf, nres, free ⊢ nres *)
  apply (exchange (D := [free; buf; nres]));
    [exact (Permutation_cons_append [buf; nres] free) |].
  exact (use_free _ _ _ _ (id_atom 1)).
Qed.

(** After a cancel the operation finishes at grade 1, with result-or-nothing,
    and the buffer comes back in both cases. *)
Lemma t5_after_cancel : seq false true [inflight; free] (Dia 1 (Plus nres One)).
Proof.
  refine (tok_cancel (j := 1) eq_refl _ _); [lia |].
  (* Tok Cnc 1 buf nres, free ⊢ ◇₁(nres ⊕ 1) *)
  apply (tok_await 1 (j := 0)).
  apply ret.
  (* buf, nres ⊕ 1, free ⊢ nres ⊕ 1 *)
  apply (exchange (D := [free; buf; Plus nres One]));
    [exact (Permutation_cons_append [buf; Plus nres One] free) |].
  exact (use_free _ _ _ _ (identity false true (Plus nres One))).
Qed.

(** Test 7. Cancel path: submit, cancel, await, both branches, free. *)
Example t7_path_cancel : seq false true [buf; read; free] (Dia 1 (Plus nres One)).
Proof.
  apply (exchange (D := [read; buf; free])); [apply perm_swap |].
  apply (lolli_L (D1 := [buf]) (D2 := [free])); [exact (id_atom 0) |].
  exact t5_after_cancel.
Qed.

Lemma ok_buf : ctx_ok buf.
Proof. left. exact I. Qed.

Lemma ok_free : ctx_ok free.
Proof. left. cbv. tauto. Qed.

Lemma ok_read : ctx_ok read.
Proof. right; right; right. exists 0, Fly, 5, 0, 1. reflexivity. Qed.

Lemma ok_goal_cancelled : forall j, goal_ok (Dia j (Plus nres One)).
Proof. intro j. right. exists j, (Plus nres One). split; [reflexivity | cbv; tauto]. Qed.

(** Test 5. The cancel rule cannot be derived from the others: without it,
    the sequent of [t5_after_cancel] has no derivation. *)
Theorem t5_cancel_needed : ~ seq false false [inflight; free] (Dia 1 (Plus nres One)).
Proof.
  intro E.
  assert (HG : Forall ctx_ok [inflight; free]).
  { apply Forall_cons;
      [right; right; left; exists Fly, 5, 0, 1; reflexivity |].
    apply Forall_cons; [exact ok_free | apply Forall_nil]. }
  pose proof (grade_lower_bound false _ _ E HG (ok_goal_cancelled 1)) as H.
  cbv in H. lia.
Qed.

(** Test 8. The cancel path cannot be faked: once the program is obliged to
    use [read], finishing at grade 1 is impossible without the cancel rule. *)
Theorem t8_no_shortcut : ~ seq false false [buf; read; free] (Dia 1 (Plus nres One)).
Proof.
  intro E.
  assert (HG : Forall ctx_ok [buf; read; free]).
  { apply Forall_cons; [exact ok_buf |].
    apply Forall_cons; [exact ok_read |].
    apply Forall_cons; [exact ok_free | apply Forall_nil]. }
  pose proof (grade_lower_bound false _ _ E HG (ok_goal_cancelled 1)) as H.
  cbv in H. lia.
Qed.

(** And the normal path cannot be claimed faster than the kernel's bound. *)
Theorem t8_normal_not_faster : ~ seq false false [buf; read; free] (Dia 4 nres).
Proof.
  intro E.
  assert (HG : Forall ctx_ok [buf; read; free]).
  { apply Forall_cons; [exact ok_buf |].
    apply Forall_cons; [exact ok_read |].
    apply Forall_cons; [exact ok_free | apply Forall_nil]. }
  assert (HC : goal_ok (Dia 4 nres))
    by (right; exists 4, nres; split; [reflexivity | exact I]).
  pose proof (grade_lower_bound false _ _ E HG HC) as H.
  cbv in H. lia.
Qed.

(** Test 3 (second half). A second cancel buys nothing: an operation already
    cancelled with bound 5 cannot be finished at grade 4, even with the
    cancel rule present. *)
Theorem t3_no_second_speedup :
  ~ seq false true [Tok Cnc 5 buf nres; free] (Dia 4 (Plus nres One)).
Proof.
  intro E.
  assert (HG : Forall ctx_ok [Tok Cnc 5 buf nres; free]).
  { apply Forall_cons;
      [right; right; left; exists Cnc, 5, 0, 1; reflexivity |].
    apply Forall_cons; [exact ok_free | apply Forall_nil]. }
  pose proof (grade_lower_bound true _ _ E HG (ok_goal_cancelled 4)) as H.
  cbv in H. lia.
Qed.

(** Test 4, concrete: the use-after-free of the proposal. While the read is
    in flight the buffer cannot be freed, and requesting a cancel does not
    change that: [free] is legal only after the await. Holds for every
    setting of the switches. *)
Lemma no_free_while_held : forall sp cn s k,
  ~ seq sp cn [Tok s k buf nres; free] One.
Proof.
  intros sp cn s k E.
  assert (HG : Forall top_or_free [Tok s k buf nres; free]).
  { apply Forall_cons;
      [right; right; exists s, k, buf, nres; reflexivity |].
    apply Forall_cons; [left; cbv; tauto | apply Forall_nil]. }
  pose proof (modal_free_inv _ _ _ _ E HG I) as Hr.
  apply Forall_cons_iff in Hr as [Hr _]. destruct Hr.
Qed.

Example t4_no_free_in_flight : forall sp cn,
  ~ seq sp cn [inflight; free] One.
Proof. intros sp cn. exact (no_free_while_held sp cn Fly 5). Qed.

Example t4_no_free_after_cancel_request : forall sp cn j,
  ~ seq sp cn [Tok Cnc j buf nres; free] One.
Proof. intros sp cn j. exact (no_free_while_held sp cn Cnc j). Qed.

(** Test 1, concrete: holding the buffer and even the result does not give
    an in-flight operation. *)
Example t1_no_fake_inflight : forall cn k,
  ~ seq false cn [buf; nres] (Tok Fly k buf nres).
Proof.
  intros cn k. apply no_fake_token.
  apply Forall_cons; [exact I |].
  apply Forall_cons; [exact I | apply Forall_nil].
Qed.

(** Test 2, concrete: without cancel an in-flight operation does not become
    a cancelled one; with cancel it does. *)
Example t2_no_cnc_without_cancel :
  ~ seq false false [inflight] (Tok Cnc 1 buf nres).
Proof.
  apply no_cnc_without_cancel.
  apply Forall_cons; [cbv; repeat split | apply Forall_nil].
Qed.

Example t2_cnc_with_cancel : seq false true [inflight] (Tok Cnc 1 buf nres).
Proof.
  refine (tok_cancel (j := 1) eq_refl _ (tok_id Cnc 1 buf nres)). lia.
Qed.

(** ** Contrast: the spawn variant ([sp = true]) fails tests 1 and 2

    With a right rule, user code that already holds the result can build an
    "in-flight" token, and can build a "cancelled" one without any cancel.
    Cut is still admissible ([CandC.cut]); what is lost is the guarantee
    that tokens come from the kernel. *)

Example spawn_fake_inflight : forall cn k,
  seq true cn [buf; nres] (Tok Fly k buf nres).
Proof.
  intros cn k.
  exact (spawn (D1 := [buf]) (D2 := [nres]) (s := Fly) k eq_refl
           (id_atom 0) (id_atom 1)).
Qed.

Example spawn_fake_cancelled : forall cn k,
  seq true cn [buf] (Tok Cnc k buf nres).
Proof.
  intros cn k.
  exact (spawn (D1 := [buf]) (D2 := []) (s := Cnc) k eq_refl
           (id_atom 0) (plus_R2 nres one_R)).
Qed.

Print Assumptions tok_not_elim.
Print Assumptions no_free_while_held.
Print Assumptions no_fake_token.
Print Assumptions no_cnc_without_cancel.
Print Assumptions cnc_rigid.
Print Assumptions t5_cancel_needed.
Print Assumptions t8_no_shortcut.
Print Assumptions t8_normal_not_faster.
Print Assumptions t3_no_second_speedup.
Print Assumptions t7_path_cancel.
Print Assumptions t6_path_normal.
