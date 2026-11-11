(** * Candidate C: an in-flight token separate from the future ◇

    Two things that v1 expresses with the single connective ◇ are split:

    - [Dia k A] (◇ₖA) stays the composable asynchronous computation
      (a graded lax modality: [ret] and [await]);
    - [Tok s k R X] is an operation held by the kernel: it holds the
      resource R and will produce X within k. Its status [s] is [Fly]
      (in flight) or [Cnc] (cancel requested).

    Token rules:

<<
    ──────────────────────────── tok_id
     Tok s k R X ⊢ Tok s k R X

        R, res s X, Δ ⊢ ◇ⱼC
    ──────────────────────────── tok_await     (res Fly X = X, res Cnc X = X ⊕ 1)
     Tok s k R X, Δ ⊢ ◇₍ₖ₊ⱼ₎C

     Tok Cnc j R X, Δ ⊢ C     j ≤ k
    ──────────────────────────────── tok_cancel     (only if cn = true)
         Tok Fly k R X, Δ ⊢ C

       Δ₁ ⊢ R      Δ₂ ⊢ res s X
    ──────────────────────────── spawn          (only if sp = true)
       Δ₁, Δ₂ ⊢ Tok s k R X
>>

    The system is parameterised by two switches so that variants can be
    compared inside one development:

    - [cn]: is the cancel rule present?
    - [sp]: can user code build tokens itself ([spawn], a right rule)?
      With [sp = false] tokens are abstract: they can only come from
      hypotheses, which stand for the kernel interface.

    There is no bind into a token: [tok_await] ends in ◇, never in [Tok].
    This is what keeps cut admissible although [tok_cancel] lowers the
    grade (compare candidates A and B).

    This file proves identity and cut admissibility for all four settings
    of the switches. The tests are in [CandC_Tests.v]. *)

From Stdlib Require Import List Permutation Lia Arith.
Import ListNotations.

(** ** Syntax *)

Inductive st : Type := Fly | Cnc.

Inductive form : Type :=
| Atom   : nat -> form
| One    : form
| Tensor : form -> form -> form
| Lolli  : form -> form -> form
| Plus   : form -> form -> form
| Dia    : nat -> form -> form
| Tok    : st -> nat -> form -> form -> form.

(** What an await delivers besides the resource: the result, or
    result-or-nothing once cancel has been requested. *)
Definition res (s : st) (X : form) : form :=
  match s with
  | Fly => X
  | Cnc => Plus X One
  end.

(** Formula size; grades and statuses are not counted. The constant 3 makes
    [res s X] smaller than [Tok s k R X]. *)
Fixpoint size (A : form) : nat :=
  match A with
  | Atom _ => 1
  | One => 1
  | Tensor A B => S (size A + size B)
  | Lolli A B => S (size A + size B)
  | Plus A B => S (size A + size B)
  | Dia _ A => S (size A)
  | Tok _ _ R X => 3 + size R + size X
  end.

Lemma size_pos : forall A, 1 <= size A.
Proof. destruct A; simpl; lia. Qed.

(** ** Rules *)

Section Rules.

Variables sp cn : bool.

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
| ret : forall D k A,
    seq D A -> seq D (Dia k A)
| await : forall D k j A C,
    seq (A :: D) (Dia j C) -> seq (Dia k A :: D) (Dia (k + j) C)
| tok_id : forall s k R X,
    seq [Tok s k R X] (Tok s k R X)
| tok_await : forall D s k j R X C,
    seq (R :: res s X :: D) (Dia j C) ->
    seq (Tok s k R X :: D) (Dia (k + j) C)
| tok_cancel : forall D k j R X C,
    cn = true -> j <= k ->
    seq (Tok Cnc j R X :: D) C ->
    seq (Tok Fly k R X :: D) C
| spawn : forall D1 D2 s k R X,
    sp = true ->
    seq D1 R -> seq D2 (res s X) ->
    seq (D1 ++ D2) (Tok s k R X).

End Rules.

Arguments id_atom {sp cn} n.
Arguments exchange {sp cn D D' C}.
Arguments one_R {sp cn}.
Arguments one_L {sp cn D C}.
Arguments tensor_R {sp cn D1 D2 A B}.
Arguments tensor_L {sp cn D A B C}.
Arguments lolli_R {sp cn D A B}.
Arguments lolli_L {sp cn D1 D2 A B C}.
Arguments plus_R1 {sp cn D A} B.
Arguments plus_R2 {sp cn D} A {B}.
Arguments plus_L {sp cn D A B C}.
Arguments ret {sp cn D} k {A}.
Arguments await {sp cn D} k {j A C}.
Arguments tok_id {sp cn} s k R X.
Arguments tok_await {sp cn D s} k {j R X C}.
Arguments tok_cancel {sp cn D k j R X C}.
Arguments spawn {sp cn D1 D2 s} k {R X}.

(** ** Identity *)

Theorem identity : forall sp cn A, seq sp cn [A] A.
Proof.
  intros sp cn.
  induction A as [n | | A IHA B IHB | A IHA B IHB | A IHA B IHB | k A IHA
                 | s k R IHR X IHX].
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
  - pose proof (await k (ret 0 IHA)) as H.
    rewrite Nat.add_0_r in H. exact H.
  - (* a token is identified by an axiom, like an atom *)
    apply tok_id.
Qed.

(** ** Permutation lemmas (as in [theories/CutElim.v]) *)

Lemma perm_cons_split : forall (a b : form) l l',
  Permutation (b :: l) (a :: l') ->
  (b = a /\ Permutation l l') \/
  (exists l1 l2, l = l1 ++ a :: l2 /\ Permutation (b :: l1 ++ l2) l').
Proof.
  intros a b l l' H.
  assert (Hin : In a (b :: l)).
  { apply (Permutation_in a (Permutation_sym H)). left. reflexivity. }
  destruct Hin as [Heq | Hin].
  - subst b. left. split; [reflexivity | exact (Permutation_cons_inv H)].
  - right. destruct (in_split a l Hin) as (l1 & l2 & ->).
    exists l1, l2. split; [reflexivity |].
    apply Permutation_sym.
    exact (Permutation_cons_app_inv (b :: l1) l2 (Permutation_sym H)).
Qed.

Lemma perm_app_split : forall (a : form) l1 l2 l',
  Permutation (l1 ++ l2) (a :: l') ->
  (exists l1', Permutation l1 (a :: l1') /\ Permutation (l1' ++ l2) l') \/
  (exists l2', Permutation l2 (a :: l2') /\ Permutation (l1 ++ l2') l').
Proof.
  intros a l1 l2 l' H.
  assert (Hin : In a (l1 ++ l2)).
  { apply (Permutation_in a (Permutation_sym H)). left. reflexivity. }
  destruct (in_app_or l1 l2 a Hin) as [Hin1 | Hin2].
  - left. destruct (in_split a l1 Hin1) as (x & y & ->).
    exists (x ++ y). split.
    + apply Permutation_sym, Permutation_middle.
    + rewrite <- app_assoc in H. simpl in H.
      rewrite <- app_assoc. apply Permutation_sym.
      exact (Permutation_cons_app_inv x (y ++ l2) (Permutation_sym H)).
  - right. destruct (in_split a l2 Hin2) as (x & y & ->).
    exists (x ++ y). split.
    + apply Permutation_sym, Permutation_middle.
    + rewrite app_assoc in H. rewrite app_assoc. apply Permutation_sym.
      exact (Permutation_cons_app_inv (l1 ++ x) y (Permutation_sym H)).
Qed.

Lemma perm_front : forall (P D1 L D2 : list form),
  Permutation (P ++ L) D2 -> Permutation (P ++ D1 ++ L) (D1 ++ D2).
Proof.
  intros P D1 L D2 H.
  transitivity (D1 ++ P ++ L).
  - rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - apply Permutation_app_head, H.
Qed.

Lemma perm_to_front : forall (P D1 L : list form),
  Permutation (D1 ++ P ++ L) (P ++ D1 ++ L).
Proof.
  intros P D1 L. apply Permutation_sym, perm_front. reflexivity.
Qed.

(** ** Relation [ext]: what the cut formula may have become on the right

    In v1, [ext] had to follow ⊕ 1 insertions deep inside a formula. Here the
    only rule that rewrites a formula in place is [tok_cancel], and it only
    touches the head of a token: status and grade. *)

Inductive ext (cn : bool) : form -> form -> Prop :=
| ext_refl : forall A, ext cn A A
| ext_cancel : forall k j R X,
    cn = true -> j <= k -> ext cn (Tok Fly k R X) (Tok Cnc j R X).

Section Cut.

Variables sp cn : bool.

Local Notation sq := (seq sp cn).

(** ** Grade of a future as an upper bound *)

Lemma dia_mono : forall D F, sq D F ->
  forall j C n, F = Dia j C -> j <= n -> sq D (Dia n C).
Proof.
  intros D F E.
  induction E as
    [ m
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
    intros j0 C1 n0 HF Hle; try discriminate HF.
  - exact (exchange Hp (IHE j0 C1 n0 HF Hle)).
  - exact (one_L (IHE j0 C1 n0 HF Hle)).
  - exact (tensor_L (IHE j0 C1 n0 HF Hle)).
  - exact (lolli_L Ea (IHb j0 C1 n0 HF Hle)).
  - exact (plus_L (IH1 j0 C1 n0 HF Hle) (IH2 j0 C1 n0 HF Hle)).
  - injection HF as _ ->. exact (ret n0 E').
  - injection HF as Hk ->.
    pose proof (IHE j C1 (n0 - k) eq_refl ltac:(lia)) as H.
    replace n0 with (k + (n0 - k)) by lia.
    exact (await k H).
  - injection HF as Hk ->.
    pose proof (IHE j C1 (n0 - k) eq_refl ltac:(lia)) as H.
    replace n0 with (k + (n0 - k)) by lia.
    exact (tok_await k H).
  - exact (tok_cancel Hcn Hjk (IHE j0 C1 n0 HF Hle)).
Qed.

(** ** Cut statement *)

Definition cut_stmt (A : form) : Prop :=
  forall D1 G D2 C A',
    ext cn A A' -> sq D1 A -> sq G C -> Permutation G (A' :: D2) ->
    sq (D1 ++ D2) C.

(** [rinfo A Δ₁] records the premises of the last rule of [Δ₁ ⊢ A] when that
    rule is a right rule, [id_atom], or an await ([await] or [tok_await]).
    For an await, what is recorded is (1) the induction hypothesis on its
    premise and (2) how to re-apply the await afterwards. *)

Definition rinfo (A : form) (D1 : list form) : Prop :=
  match A with
  | Atom _ => True
  | One => D1 = []
  | Tensor Y Z => exists Da Db, D1 = Da ++ Db /\ sq Da Y /\ sq Db Z
  | Lolli Y Z => sq (Y :: D1) Z
  | Plus P Q => sq D1 P \/ sq D1 Q
  | Dia k Y =>
      sq D1 Y \/
      exists k1 j1 Dp, k = k1 + j1 /\
        (forall G C D2, sq G C -> Permutation G (Dia j1 Y :: D2) ->
           sq (Dp ++ D2) C) /\
        (forall D2 j' C', sq (Dp ++ D2) (Dia j' C') ->
           sq (D1 ++ D2) (Dia (k1 + j') C'))
  | Tok s k R X =>
      exists Da Db, D1 = Da ++ Db /\ sq Da R /\ sq Db (res s X) /\ sp = true
  end.

(** Principal case for a token built by [spawn] and consumed by
    [tok_await]: two cuts on smaller formulas, then raise the grade. *)
Lemma tok_await_cut : forall s k j Rr Xx Da Db G C0,
  (forall B, size B <= size Rr + size Xx + 2 -> cut_stmt B) ->
  sq Da Rr -> sq Db (res s Xx) ->
  sq (Rr :: res s Xx :: G) (Dia j C0) ->
  sq ((Da ++ Db) ++ G) (Dia (k + j) C0).
Proof.
  intros s k j Rr Xx Da Db G C0 IH DR DX E'.
  assert (Hs1 : size (res s Xx) <= size Rr + size Xx + 2)
    by (destruct s; simpl; lia).
  assert (Hs2 : size Rr <= size Rr + size Xx + 2) by lia.
  assert (s1 : sq (Db ++ Rr :: G) (Dia j C0)).
  { apply (IH (res s Xx) Hs1 Db (Rr :: res s Xx :: G) (Rr :: G) (Dia j C0)
              (res s Xx) (ext_refl cn _) DX E').
    apply perm_swap. }
  assert (s2 : sq (Da ++ Db ++ G) (Dia j C0)).
  { apply (IH Rr Hs2 Da (Db ++ Rr :: G) (Db ++ G) (Dia j C0) Rr
              (ext_refl cn _) DR s1).
    apply Permutation_sym, Permutation_middle. }
  rewrite <- app_assoc.
  exact (dia_mono _ _ s2 j C0 (k + j) eq_refl ltac:(lia)).
Qed.

(** ** Induction on the right derivation *)

Lemma cut_E : forall A D1,
  (forall B, size B < size A -> cut_stmt B) ->
  rinfo A D1 -> sq D1 A ->
  forall G C, sq G C ->
  forall A' D2, ext cn A A' -> Permutation G (A' :: D2) -> sq (D1 ++ D2) C.
Proof.
  intros A D1 IH R Dd G C E.
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
    intros A' D2 Hx H.
  - (* id_atom *)
    apply Permutation_length_1_inv in H. injection H as -> ->.
    inversion Hx; subst.
    rewrite app_nil_r. exact Dd.
  - (* exchange *)
    exact (IHE A' D2 Hx (Permutation_trans Hp H)).
  - (* one_R *)
    exfalso. exact (Permutation_nil_cons H).
  - (* one_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'. inversion Hx; subst. simpl in R. subst D1.
      exact (exchange Hp E').
    + specialize (IHE A' (l1 ++ l2) Hx (Permutation_sym (Permutation_middle _ _ _))).
      exact (exchange (perm_front [One] D1 _ D2 Hp) (one_L IHE)).
  - (* tensor_R *)
    destruct (perm_app_split _ _ _ _ H) as [(l1 & H1 & H2) | (l2 & H1 & H2)].
    + specialize (IHa A' l1 Hx H1).
      apply (exchange (D := (D1 ++ l1) ++ Gb)).
      * rewrite <- app_assoc. apply Permutation_app_head, H2.
      * exact (tensor_R IHa Eb).
    + specialize (IHb A' l2 Hx H1).
      exact (exchange (perm_front Ga D1 l2 D2 H2) (tensor_R Ea IHb)).
  - (* tensor_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'. inversion Hx; subst.
      simpl in R. destruct R as (Da & Db & -> & DX & DY).
      assert (s1 : sq (Db ++ X :: G) C0).
      { apply (IH Y ltac:(simpl; lia) Db (X :: Y :: G) (X :: G) C0 Y
                  (ext_refl cn Y) DY E').
        apply perm_swap. }
      assert (s2 : sq (Da ++ Db ++ G) C0).
      { apply (IH X ltac:(simpl; lia) Da (Db ++ X :: G) (Db ++ G) C0 X
                  (ext_refl cn X) DX s1).
        apply Permutation_sym, Permutation_middle. }
      rewrite <- app_assoc.
      exact (exchange (Permutation_app_head _ (Permutation_app_head _ Hp)) s2).
    + specialize (IHE A' (X :: Y :: l1 ++ l2) Hx
                      (Permutation_sym (Permutation_middle (X :: Y :: l1) _ _))).
      apply (exchange (perm_front [Tensor X Y] D1 _ D2 Hp)).
      apply tensor_L.
      exact (exchange (perm_to_front [X; Y] D1 _) IHE).
  - (* lolli_R *)
    assert (H' : Permutation (X :: G) (A' :: X :: D2)).
    { transitivity (X :: A' :: D2); [apply perm_skip, H | apply perm_swap]. }
    specialize (IHE A' (X :: D2) Hx H').
    apply lolli_R.
    exact (exchange (Permutation_sym (Permutation_middle _ _ _)) IHE).
  - (* lolli_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & Heq & Hp)].
    + subst A'. inversion Hx; subst.
      simpl in R.
      assert (s1 : sq (Ga ++ D1) Y).
      { exact (IH X ltac:(simpl; lia) Ga (X :: D1) D1 Y X (ext_refl cn X) Ea R
                  (Permutation_refl _)). }
      assert (s2 : sq ((Ga ++ D1) ++ Gb) C0).
      { exact (IH Y ltac:(simpl; lia) (Ga ++ D1) (Y :: Gb) Gb C0 Y
                  (ext_refl cn Y) s1 Eb (Permutation_refl _)). }
      rewrite <- app_assoc in s2.
      exact (exchange (perm_front Ga D1 Gb D2 Hp) s2).
    + assert (Hab : Permutation (Ga ++ Gb) (A' :: l1 ++ l2)).
      { rewrite Heq. apply Permutation_sym, Permutation_middle. }
      destruct (perm_app_split _ _ _ _ Hab) as [(la & H1 & H2) | (lb & H1 & H2)].
      * specialize (IHa A' la Hx H1).
        apply (exchange (D := Lolli X Y :: D1 ++ la ++ Gb)).
        -- apply (perm_front [Lolli X Y] D1 (la ++ Gb) D2).
           exact (Permutation_trans (perm_skip _ H2) Hp).
        -- rewrite app_assoc. exact (lolli_L IHa Eb).
      * assert (H' : Permutation (Y :: Gb) (A' :: Y :: lb)).
        { transitivity (Y :: A' :: lb); [apply perm_skip, H1 | apply perm_swap]. }
        specialize (IHb A' (Y :: lb) Hx H').
        apply (exchange (perm_front (Lolli X Y :: Ga) D1 lb D2
                           (Permutation_trans (perm_skip _ H2) Hp))).
        apply (lolli_L Ea).
        exact (exchange (Permutation_sym (Permutation_middle _ _ _)) IHb).
  - (* plus_R1 *)
    exact (plus_R1 Y (IHE A' D2 Hx H)).
  - (* plus_R2 *)
    exact (plus_R2 X (IHE A' D2 Hx H)).
  - (* plus_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'. inversion Hx; subst.
      simpl in R. destruct R as [DP | DQ].
      * exact (exchange (Permutation_app_head _ Hp)
                 (IH X ltac:(simpl; lia) D1 (X :: G) G C0 X (ext_refl cn X) DP E1
                     (Permutation_refl _))).
      * exact (exchange (Permutation_app_head _ Hp)
                 (IH Y ltac:(simpl; lia) D1 (Y :: G) G C0 Y (ext_refl cn Y) DQ E2
                     (Permutation_refl _))).
    + specialize (IH1 A' (X :: l1 ++ l2) Hx
                      (Permutation_sym (Permutation_middle (X :: l1) _ _))).
      specialize (IH2 A' (Y :: l1 ++ l2) Hx
                      (Permutation_sym (Permutation_middle (Y :: l1) _ _))).
      apply (exchange (perm_front [Plus X Y] D1 _ D2 Hp)).
      apply plus_L.
      * exact (exchange (perm_to_front [X] D1 _) IH1).
      * exact (exchange (perm_to_front [Y] D1 _) IH2).
  - (* ret *)
    exact (ret k (IHE A' D2 Hx H)).
  - (* await *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'. inversion Hx; subst.
      simpl in R. destruct R as [DY | (k1 & j1 & Dp & Hk & Hcut & Hwrap)].
      * (* ret versus await *)
        assert (s : sq (D1 ++ G) (Dia j C0)).
        { exact (IH X ltac:(simpl; lia) D1 (X :: G) G (Dia j C0) X
                    (ext_refl cn X) DY E' (Permutation_refl _)). }
        apply (exchange (Permutation_app_head _ Hp)).
        exact (dia_mono _ _ s j C0 (k + j) eq_refl ltac:(lia)).
      * (* await versus await: commute into the premise of the left one *)
        assert (s : sq (Dp ++ G) (Dia (j1 + j) C0)).
        { exact (Hcut (Dia j1 X :: G) (Dia (j1 + j) C0) G (await j1 E')
                      (Permutation_refl _)). }
        rewrite Hk, <- Nat.add_assoc.
        exact (exchange (Permutation_app_head _ Hp) (Hwrap G (j1 + j) C0 s)).
    + specialize (IHE A' (X :: l1 ++ l2) Hx
                      (Permutation_sym (Permutation_middle (X :: l1) _ _))).
      apply (exchange (perm_front [Dia k X] D1 _ D2 Hp)).
      apply await.
      exact (exchange (perm_to_front [X] D1 _) IHE).
  - (* tok_id: the right derivation is just the token itself *)
    apply Permutation_length_1_inv in H. injection H as -> ->.
    rewrite app_nil_r.
    inversion Hx; subst.
    + exact Dd.
    + (* the token was spawned as Fly and has been cancelled since:
         rebuild it as Cnc, the result goes to the left branch of ⊕ *)
      simpl in R. destruct R as (Da & Db & -> & DR & DX & Hsp).
      exact (spawn (s := Cnc) k Hsp DR (plus_R1 One DX)).
  - (* tok_await *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'. inversion Hx; subst.
      * (* spawn versus tok_await *)
        simpl in R. destruct R as (Da & Db & -> & DR & DX & Hsp).
        apply (exchange (Permutation_app_head _ Hp)).
        apply (tok_await_cut s k j Rr Xx Da Db G C0); try assumption.
        intros B HB. apply IH. simpl. lia.
      * (* spawn (as Fly), cancel, then tok_await (as Cnc) *)
        simpl in R. destruct R as (Da & Db & -> & DR & DX & Hsp).
        apply (exchange (Permutation_app_head _ Hp)).
        apply (tok_await_cut Cnc k j Rr Xx Da Db G C0); try assumption.
        -- intros B HB. apply IH. simpl. lia.
        -- exact (plus_R1 One DX).
    + specialize (IHE A' (Rr :: res s Xx :: l1 ++ l2) Hx
                      (Permutation_sym
                         (Permutation_middle (Rr :: res s Xx :: l1) _ _))).
      apply (exchange (perm_front [Tok s k Rr Xx] D1 _ D2 Hp)).
      apply tok_await.
      exact (exchange (perm_to_front [Rr; res s Xx] D1 _) IHE).
  - (* tok_cancel *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + (* cancel on the cut formula: the right side continues with Cnc *)
      subst A'. inversion Hx; subst.
      exact (IHE (Tok Cnc j Rr Xx) D2 (ext_cancel cn k j Rr Xx Hcn Hjk)
                 (perm_skip _ Hp)).
    + specialize (IHE A' (Tok Cnc j Rr Xx :: l1 ++ l2) Hx
                      (Permutation_sym
                         (Permutation_middle (Tok Cnc j Rr Xx :: l1) _ _))).
      apply (exchange (perm_front [Tok Fly k Rr Xx] D1 _ D2 Hp)).
      apply (tok_cancel Hcn Hjk).
      exact (exchange (perm_to_front [Tok Cnc j Rr Xx] D1 _) IHE).
  - (* spawn *)
    destruct (perm_app_split _ _ _ _ H) as [(l1 & H1 & H2) | (l2 & H1 & H2)].
    + specialize (IHa A' l1 Hx H1).
      apply (exchange (D := (D1 ++ l1) ++ Gb)).
      * rewrite <- app_assoc. apply Permutation_app_head, H2.
      * exact (spawn k Hsp IHa Eb).
    + specialize (IHb A' l2 Hx H1).
      exact (exchange (perm_front Ga D1 l2 D2 H2) (spawn k Hsp Ea IHb)).
Qed.

(** ** Induction on the left derivation and on formula size *)

Lemma cut_aux : forall n A, size A <= n -> cut_stmt A.
Proof.
  induction n as [| n IHn]; intros A Hs.
  - pose proof (size_pos A). lia.
  - intros D1 G D2 C A' Hx Dd. revert Hs G D2 C A' Hx.
    induction Dd as
      [ m
      | Dl Dl' A0 Hp Dd' IHD
      |
      | Dl A0 Dd' IHD
      | Dl1 Dl2 X Y Da IHa Db IHb
      | Dl X Y A0 Dd' IHD
      | Dl X Y Dd' IHD
      | Dl1 Dl2 X Y A0 Da IHa Db IHb
      | Dl X Y Dd' IHD
      | Dl X Y Dd' IHD
      | Dl X Y A0 Dd1 IH1 Dd2 IH2
      | Dl k X Dd' IHD
      | Dl k j X A0 Dd' IHD
      | s k Rr Xx
      | Dl s k j Rr Xx A0 Dd' IHD
      | Dl k j Rr Xx A0 Hcn Hjk Dd' IHD
      | Dl1 Dl2 s k Rr Xx Hsp Da IHa Db IHb ];
      intros Hs G0 D2 C0 A' Hx E H.
    + (* id_atom *)
      refine (cut_E (Atom m) [Atom m] _ I (id_atom m) G0 C0 E A' D2 Hx H).
      intros B Hlt. pose proof (size_pos B). simpl in Hlt. lia.
    + (* exchange *)
      exact (exchange (Permutation_app_tail _ Hp) (IHD Hs G0 D2 C0 A' Hx E H)).
    + (* one_R *)
      refine (cut_E One [] _ eq_refl one_R G0 C0 E A' D2 Hx H).
      intros B Hlt. pose proof (size_pos B). simpl in Hlt. lia.
    + (* one_L *)
      exact (one_L (IHD Hs G0 D2 C0 A' Hx E H)).
    + (* tensor_R *)
      refine (cut_E (Tensor X Y) (Dl1 ++ Dl2) _ _ (tensor_R Da Db) G0 C0 E A' D2 Hx H).
      * intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
      * exists Dl1, Dl2. auto.
    + (* tensor_L *)
      exact (tensor_L (IHD Hs G0 D2 C0 A' Hx E H)).
    + (* lolli_R *)
      refine (cut_E (Lolli X Y) Dl _ Dd' (lolli_R Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
    + (* lolli_L *)
      simpl. rewrite <- app_assoc.
      exact (lolli_L Da (IHb Hs G0 D2 C0 A' Hx E H)).
    + (* plus_R1 *)
      refine (cut_E (Plus X Y) Dl _ (or_introl Dd') (plus_R1 Y Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
    + (* plus_R2 *)
      refine (cut_E (Plus X Y) Dl _ (or_intror Dd') (plus_R2 X Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
    + (* plus_L *)
      exact (plus_L (IH1 Hs G0 D2 C0 A' Hx E H) (IH2 Hs G0 D2 C0 A' Hx E H)).
    + (* ret *)
      refine (cut_E (Dia k X) Dl _ (or_introl Dd') (ret k Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
    + (* await *)
      refine (cut_E (Dia (k + j) A0) (Dia k X :: Dl) _ _ (await k Dd')
                G0 C0 E A' D2 Hx H).
      * intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
      * right. exists k, j, (X :: Dl). split; [reflexivity | split].
        -- intros G1 C1 D3 E1 H1.
           exact (IHD Hs G1 D3 C1 (Dia j A0) (ext_refl cn _) E1 H1).
        -- intros D3 j' C' h. exact (await k h).
    + (* tok_id: cutting against the identity axiom changes nothing,
         except that the right side may have cancelled the token *)
      inversion Hx; subst.
      * exact (exchange H E).
      * match goal with
        | Hc : cn = true, Hl : _ <= _ |- _ =>
            exact (tok_cancel Hc Hl (exchange H E))
        end.
    + (* tok_await *)
      refine (cut_E (Dia (k + j) A0) (Tok s k Rr Xx :: Dl) _ _ (tok_await k Dd')
                G0 C0 E A' D2 Hx H).
      * intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
      * right. exists k, j, (Rr :: res s Xx :: Dl). split; [reflexivity | split].
        -- intros G1 C1 D3 E1 H1.
           exact (IHD Hs G1 D3 C1 (Dia j A0) (ext_refl cn _) E1 H1).
        -- intros D3 j' C' h. exact (tok_await k h).
    + (* tok_cancel *)
      exact (tok_cancel Hcn Hjk (IHD Hs G0 D2 C0 A' Hx E H)).
    + (* spawn *)
      refine (cut_E (Tok s k Rr Xx) (Dl1 ++ Dl2) _ _ (spawn k Hsp Da Db)
                G0 C0 E A' D2 Hx H).
      * intros B Hlt. apply IHn. simpl in Hs, Hlt. lia.
      * exists Dl1, Dl2. auto.
Qed.

Theorem cut_admissible : forall A, cut_stmt A.
Proof. intro A. exact (cut_aux (size A) A (le_n _)). Qed.

(** Normal form: cut formula at the head of the right context. *)
Corollary cut : forall D1 D2 A C,
  sq D1 A -> sq (A :: D2) C -> sq (D1 ++ D2) C.
Proof.
  intros D1 D2 A C Dd E.
  exact (cut_admissible A D1 (A :: D2) D2 C A (ext_refl cn A) Dd E
           (Permutation_refl _)).
Qed.

End Cut.

Print Assumptions cut.
