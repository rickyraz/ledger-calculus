(** * Cut admissibility

    Strategi: induksi luar pada ukuran formula cut ([size A]), lalu induksi
    struktural pada derivasi kiri [Dd : Δ₁ ⊢ A], lalu (bila [Dd] berakhir
    dengan aturan kanan untuk A atau [id_atom]) induksi struktural pada
    derivasi kanan [E : Γ ⊢ C] di lemma [cut_E]. Induksi struktural pada
    derivasi menggantikan induksi pada tinggi derivasi: setiap pemanggilan
    hipotesis induksi memakai sub-derivasi langsung.

    Cut dirumuskan untuk Γ yang merupakan permutasi dari [A :: Δ₂], sehingga
    kasus [exchange] di kedua sisi tidak perlu memindahkan formula cut. *)

From Stdlib Require Import List Permutation Lia.
From LedgerCalculus Require Import Syntax Sequent.
Import ListNotations.

Definition cut_stmt (aw : bool) (A : form) : Prop :=
  forall D1 G D2 C,
    seq aw D1 A -> seq aw G C -> Permutation G (A :: D2) ->
    seq aw (D1 ++ D2) C.

(** ** Lemma permutasi *)

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

(** ** Inversi kanan

    [right_inv aw A Δ₁] mencatat premis aturan kanan (atau [id_atom]) yang
    menurunkan [Δ₁ ⊢ A]. Ini yang dibutuhkan kasus principal. *)

Definition right_inv (aw : bool) (A : form) (D : list form) : Prop :=
  match A with
  | Atom n => D = [Atom n]
  | One => D = []
  | Tensor X Y => exists Da Db, D = Da ++ Db /\ seq aw Da X /\ seq aw Db Y
  | Lolli X Y => seq aw (X :: D) Y
  | Dia _ X => seq aw D X
  end.

Lemma size_pos : forall A, 1 <= size A.
Proof. destruct A; simpl; lia. Qed.

(** ** Induksi pada derivasi kanan *)

Lemma cut_E : forall aw A D1,
  (forall A', size A' < size A -> cut_stmt aw A') ->
  right_inv aw A D1 -> seq aw D1 A ->
  forall G C, seq aw G C ->
  forall D2, Permutation G (A :: D2) -> seq aw (D1 ++ D2) C.
Proof.
  intros aw A D1 IH R Dd G C E.
  induction E as
    [ n
    | G G' C0 Hp E' IHE
    |
    | G C0 E' IHE
    | Ga Gb X Y Ea IHa Eb IHb
    | G X Y C0 E' IHE
    | G X Y E' IHE
    | Ga Gb X Y C0 Ea IHa Eb IHb
    | G k X E' IHE
    | G k X C0 Haw E' IHE
    | G k X C0 E' IHE ];
    intros D2 H.
  - (* id_atom *)
    apply Permutation_length_1_inv in H. injection H as -> ->.
    rewrite app_nil_r. exact Dd.
  - (* exchange *)
    exact (IHE D2 (Permutation_trans Hp H)).
  - (* one_R *)
    exfalso. exact (Permutation_nil_cons H).
  - (* one_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + (* principal *)
      subst A. simpl in R. subst D1. exact (exchange Hp E').
    + specialize (IHE (l1 ++ l2) (Permutation_sym (Permutation_middle _ _ _))).
      exact (exchange (perm_front [One] D1 _ D2 Hp) (one_L IHE)).
  - (* tensor_R *)
    destruct (perm_app_split _ _ _ _ H) as [(l1 & H1 & H2) | (l2 & H1 & H2)].
    + specialize (IHa l1 H1).
      apply (exchange (D := (D1 ++ l1) ++ Gb)).
      * rewrite <- app_assoc. apply Permutation_app_head, H2.
      * exact (tensor_R IHa Eb).
    + specialize (IHb l2 H1).
      exact (exchange (perm_front Ga D1 l2 D2 H2) (tensor_R Ea IHb)).
  - (* tensor_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + (* principal *)
      subst A. simpl in R. destruct R as (Da & Db & -> & DX & DY).
      assert (s1 : seq aw (Db ++ X :: G) C0).
      { apply (IH Y ltac:(simpl; lia) Db (X :: Y :: G) (X :: G) C0 DY E').
        apply perm_swap. }
      assert (s2 : seq aw (Da ++ Db ++ G) C0).
      { apply (IH X ltac:(simpl; lia) Da (Db ++ X :: G) (Db ++ G) C0 DX s1).
        apply Permutation_sym, Permutation_middle. }
      rewrite <- app_assoc.
      exact (exchange (Permutation_app_head _ (Permutation_app_head _ Hp)) s2).
    + specialize (IHE (X :: Y :: l1 ++ l2)
                      (Permutation_sym (Permutation_middle (X :: Y :: l1) _ _))).
      apply (exchange (perm_front [Tensor X Y] D1 _ D2 Hp)).
      apply tensor_L.
      exact (exchange (perm_to_front [X; Y] D1 _) IHE).
  - (* lolli_R *)
    assert (H' : Permutation (X :: G) (A :: X :: D2)).
    { transitivity (X :: A :: D2); [apply perm_skip, H | apply perm_swap]. }
    specialize (IHE (X :: D2) H').
    apply lolli_R.
    exact (exchange (Permutation_sym (Permutation_middle _ _ _)) IHE).
  - (* lolli_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & Heq & Hp)].
    + (* principal *)
      subst A. simpl in R.
      assert (s1 : seq aw (Ga ++ D1) Y).
      { exact (IH X ltac:(simpl; lia) Ga (X :: D1) D1 Y Ea R
                  (Permutation_refl _)). }
      assert (s2 : seq aw ((Ga ++ D1) ++ Gb) C0).
      { exact (IH Y ltac:(simpl; lia) (Ga ++ D1) (Y :: Gb) Gb C0 s1 Eb
                  (Permutation_refl _)). }
      rewrite <- app_assoc in s2.
      exact (exchange (perm_front Ga D1 Gb D2 Hp) s2).
    + assert (Hab : Permutation (Ga ++ Gb) (A :: l1 ++ l2)).
      { rewrite Heq. apply Permutation_sym, Permutation_middle. }
      destruct (perm_app_split _ _ _ _ Hab) as [(la & H1 & H2) | (lb & H1 & H2)].
      * specialize (IHa la H1).
        apply (exchange (D := Lolli X Y :: D1 ++ la ++ Gb)).
        -- apply (perm_front [Lolli X Y] D1 (la ++ Gb) D2).
           exact (Permutation_trans (perm_skip _ H2) Hp).
        -- rewrite app_assoc. exact (lolli_L IHa Eb).
      * assert (H' : Permutation (Y :: Gb) (A :: Y :: lb)).
        { transitivity (Y :: A :: lb); [apply perm_skip, H1 | apply perm_swap]. }
        specialize (IHb (Y :: lb) H').
        apply (exchange (perm_front (Lolli X Y :: Ga) D1 lb D2
                           (Permutation_trans (perm_skip _ H2) Hp))).
        apply (lolli_L Ea).
        exact (exchange (Permutation_sym (Permutation_middle _ _ _)) IHb).
  - (* submit *)
    exact (submit k (IHE D2 H)).
  - (* await *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + (* principal *)
      subst A. simpl in R.
      assert (s : seq aw (D1 ++ G) C0).
      { exact (IH X ltac:(simpl; lia) D1 (X :: G) G C0 R E'
                  (Permutation_refl _)). }
      exact (exchange (Permutation_app_head _ Hp) s).
    + specialize (IHE (X :: l1 ++ l2)
                      (Permutation_sym (Permutation_middle (X :: l1) _ _))).
      apply (exchange (perm_front [Dia k X] D1 _ D2 Hp)).
      apply (await Haw).
      exact (exchange (perm_to_front [X] D1 _) IHE).
  - (* cancel *)
    exact (IHE D2 H).
Qed.

(** ** Induksi pada derivasi kiri dan pada ukuran formula *)

Lemma cut_aux : forall n aw A, size A <= n -> cut_stmt aw A.
Proof.
  induction n as [| n IHn]; intros aw A Hs.
  - pose proof (size_pos A). lia.
  - intros D1 G D2 C Dd. revert Hs G D2 C.
    induction Dd as
      [ m
      | Dl Dl' A0 Hp Dd' IHD
      |
      | Dl A0 Dd' IHD
      | Dl1 Dl2 X Y Da IHa Db IHb
      | Dl X Y A0 Dd' IHD
      | Dl X Y Dd' IHD
      | Dl1 Dl2 X Y A0 Da IHa Db IHb
      | Dl k X Dd' IHD
      | Dl k X A0 Haw Dd' IHD
      | Dl k X A0 Dd' IHD ];
      intros Hs G0 D2 C0 E H.
    + (* id_atom *)
      refine (cut_E aw (Atom m) [Atom m] _ _ _ G0 C0 E D2 H).
      * intros A' Hlt. pose proof (size_pos A'). simpl in Hlt. lia.
      * reflexivity.
      * apply id_atom.
    + (* exchange *)
      exact (exchange (Permutation_app_tail _ Hp) (IHD Hs G0 D2 C0 E H)).
    + (* one_R *)
      refine (cut_E aw One [] _ _ _ G0 C0 E D2 H).
      * intros A' Hlt. pose proof (size_pos A'). simpl in Hlt. lia.
      * reflexivity.
      * apply one_R.
    + (* one_L *)
      exact (one_L (IHD Hs G0 D2 C0 E H)).
    + (* tensor_R *)
      refine (cut_E aw (Tensor X Y) (Dl1 ++ Dl2) _ _ _ G0 C0 E D2 H).
      * intros A' Hlt. apply IHn. lia.
      * exists Dl1, Dl2. auto.
      * exact (tensor_R Da Db).
    + (* tensor_L *)
      exact (tensor_L (IHD Hs G0 D2 C0 E H)).
    + (* lolli_R *)
      refine (cut_E aw (Lolli X Y) Dl _ _ _ G0 C0 E D2 H).
      * intros A' Hlt. apply IHn. lia.
      * exact Dd'.
      * exact (lolli_R Dd').
    + (* lolli_L *)
      simpl. rewrite <- app_assoc.
      exact (lolli_L Da (IHb Hs G0 D2 C0 E H)).
    + (* submit *)
      refine (cut_E aw (Dia k X) Dl _ _ _ G0 C0 E D2 H).
      * intros A' Hlt. apply IHn. lia.
      * exact Dd'.
      * exact (submit k Dd').
    + (* await *)
      exact (await Haw (IHD Hs G0 D2 C0 E H)).
    + (* cancel *)
      exact (cancel (IHD Hs G0 D2 C0 E H)).
Qed.

Theorem cut_admissible : forall aw A, cut_stmt aw A.
Proof. intros aw A. exact (cut_aux (size A) aw A (le_n _)). Qed.

(** Bentuk biasa: formula cut di kepala konteks kanan. *)
Corollary cut : forall aw D1 D2 A C,
  seq aw D1 A -> seq aw (A :: D2) C -> seq aw (D1 ++ D2) C.
Proof.
  intros aw D1 D2 A C Dd E.
  exact (cut_admissible aw A D1 (A :: D2) D2 C Dd E (Permutation_refl _)).
Qed.
