(** * Cut admissibility

    Strategi: induksi luar pada ukuran formula cut di sisi kiri ([size A]),
    lalu induksi struktural pada derivasi kiri [Dd : Δ₁ ⊢ A]. Aturan kiri
    (selain [await]), [cancel], dan [exchange] di [Dd] dikomutasikan langsung.
    Bila [Dd] berakhir dengan aturan kanan, [id_atom], atau [await], premisnya
    dicatat di [rinfo] dan dilakukan induksi struktural pada derivasi kanan
    [E : Γ ⊢ C] di lemma [cut_E].

    Dua hal khusus untuk sistem lax:
    - [await] di [Dd] tidak bisa dikomutasikan sebelum [E] juga berakhir di
      future, jadi ia ditangani di dalam [cut_E], saat [E] principal pada
      formula cut (kasus [await] terhadap [await]).
    - [cancel] di [E] mengganti formula cut ◇ₖ(R ⊗ X) dengan ◇ₖ(R ⊗ (X ⊕ 1)),
      yang lebih besar. Karena itu formula cut di sisi kanan boleh berupa
      [A'] dengan [ext A A']: A' adalah A dengan sebagian subformula positif X
      diganti X ⊕ 1. Ukuran induksi tetap ukuran A di sisi kiri. *)

From Stdlib Require Import List Permutation Lia Arith.
From LedgerCalculus Require Import Syntax Sequent.
Import ListNotations.

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

(** ** Relasi [ext]: penyisipan ⊕ 1 di posisi positif *)

Inductive ext : form -> form -> Prop :=
| ext_atom : forall n, ext (Atom n) (Atom n)
| ext_one : ext One One
| ext_tensor : forall A A' B B',
    ext A A' -> ext B B' -> ext (Tensor A B) (Tensor A' B')
| ext_lolli : forall A B B', ext B B' -> ext (Lolli A B) (Lolli A B')
| ext_plus : forall A A' B B',
    ext A A' -> ext B B' -> ext (Plus A B) (Plus A' B')
| ext_dia : forall k A A', ext A A' -> ext (Dia k A) (Dia k A')
| ext_inl : forall A A', ext A A' -> ext A (Plus A' One).

Lemma ext_refl : forall A, ext A A.
Proof. induction A; constructor; assumption. Qed.

Lemma ext_atom_inv : forall A n, ext A (Atom n) -> A = Atom n.
Proof. intros A n H. inversion H. reflexivity. Qed.

Lemma ext_one_inv : forall A, ext A One -> A = One.
Proof. intros A H. inversion H. reflexivity. Qed.

Lemma ext_tensor_inv : forall A X Y, ext A (Tensor X Y) ->
  exists X0 Y0, A = Tensor X0 Y0 /\ ext X0 X /\ ext Y0 Y.
Proof. intros A X Y H. inversion H; subst. eauto. Qed.

Lemma ext_lolli_inv : forall A X Y, ext A (Lolli X Y) ->
  exists Y0, A = Lolli X Y0 /\ ext Y0 Y.
Proof. intros A X Y H. inversion H; subst. eauto. Qed.

Lemma ext_plus_inv : forall A P Q, ext A (Plus P Q) ->
  (exists P0 Q0, A = Plus P0 Q0 /\ ext P0 P /\ ext Q0 Q) \/ (Q = One /\ ext A P).
Proof. intros A P Q H. inversion H; subst; eauto 6. Qed.

Lemma ext_dia_inv : forall A k Y, ext A (Dia k Y) ->
  exists Y0, A = Dia k Y0 /\ ext Y0 Y.
Proof. intros A k Y H. inversion H; subst. eauto. Qed.

(** Langkah [cancel] mempertahankan [ext]. *)
Lemma ext_cancel_step : forall A k R X,
  ext A (Dia k (Tensor R X)) -> ext A (Dia k (Tensor R (Plus X One))).
Proof.
  intros A k R X H.
  destruct (ext_dia_inv _ _ _ H) as (B & -> & HB).
  destruct (ext_tensor_inv _ _ _ HB) as (R0 & X0 & -> & HR & HX).
  apply ext_dia, ext_tensor; [exact HR | apply ext_inl, HX].
Qed.

Lemma size_pos : forall A, 1 <= size A.
Proof. destruct A; simpl; lia. Qed.

(** ** Grade sebagai batas atas *)

Lemma dia_mono : forall D F, seq D F ->
  forall j C n, F = Dia j C -> j <= n -> seq D (Dia n C).
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
    | G k Rr Xx C0 E' IHE ];
    intros j0 C1 n0 HF Hle; try discriminate HF.
  - exact (exchange Hp (IHE j0 C1 n0 HF Hle)).
  - exact (one_L (IHE j0 C1 n0 HF Hle)).
  - exact (tensor_L (IHE j0 C1 n0 HF Hle)).
  - exact (lolli_L Ea (IHb j0 C1 n0 HF Hle)).
  - exact (plus_L (IH1 j0 C1 n0 HF Hle) (IH2 j0 C1 n0 HF Hle)).
  - injection HF as _ ->. exact (submit n0 E').
  - injection HF as Hk ->.
    pose proof (IHE j C1 (n0 - k) eq_refl ltac:(lia)) as H.
    replace n0 with (k + (n0 - k)) by lia.
    exact (await k H).
  - exact (cancel (IHE j0 C1 n0 HF Hle)).
Qed.

(** ** Pernyataan cut *)

Definition cut_stmt (A : form) : Prop :=
  forall D1 G D2 C A',
    ext A A' -> seq D1 A -> seq G C -> Permutation G (A' :: D2) ->
    seq (D1 ++ D2) C.

(** [rinfo A Δ₁] mencatat premis aturan terakhir dari [Δ₁ ⊢ A] bila aturan
    itu aturan kanan, [id_atom], atau [await]. Untuk [await], yang dicatat
    adalah hipotesis induksi pada premisnya. *)

Definition rinfo (A : form) (D1 : list form) : Prop :=
  match A with
  | Atom _ => True
  | One => D1 = []
  | Tensor Y Z => exists Da Db, D1 = Da ++ Db /\ seq Da Y /\ seq Db Z
  | Lolli Y Z => seq (Y :: D1) Z
  | Plus P Q => seq D1 P \/ seq D1 Q
  | Dia k Y =>
      seq D1 Y \/
      exists k1 j1 X D, k = k1 + j1 /\ D1 = Dia k1 X :: D /\
        (forall G C A' D2, ext (Dia j1 Y) A' -> seq G C ->
           Permutation G (A' :: D2) -> seq ((X :: D) ++ D2) C)
  end.

(** ** Induksi pada derivasi kanan *)

Lemma cut_E : forall A D1,
  (forall B, size B < size A -> cut_stmt B) ->
  rinfo A D1 -> seq D1 A ->
  forall G C, seq G C ->
  forall A' D2, ext A A' -> Permutation G (A' :: D2) -> seq (D1 ++ D2) C.
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
    | G k Rr Xx C0 E' IHE ];
    intros A' D2 Hx H.
  - (* id_atom *)
    apply Permutation_length_1_inv in H. injection H as -> ->.
    rewrite (ext_atom_inv _ _ Hx) in Dd.
    rewrite app_nil_r. exact Dd.
  - (* exchange *)
    exact (IHE A' D2 Hx (Permutation_trans Hp H)).
  - (* one_R *)
    exfalso. exact (Permutation_nil_cons H).
  - (* one_L *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'. rewrite (ext_one_inv _ Hx) in R. simpl in R. subst D1.
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
    + subst A'. destruct (ext_tensor_inv _ _ _ Hx) as (X0 & Y0 & -> & HX & HY).
      simpl in R. destruct R as (Da & Db & -> & DX & DY).
      assert (s1 : seq (Db ++ X :: G) C0).
      { apply (IH Y0 ltac:(simpl; lia) Db (X :: Y :: G) (X :: G) C0 Y HY DY E').
        apply perm_swap. }
      assert (s2 : seq (Da ++ Db ++ G) C0).
      { apply (IH X0 ltac:(simpl; lia) Da (Db ++ X :: G) (Db ++ G) C0 X HX DX s1).
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
    + subst A'. destruct (ext_lolli_inv _ _ _ Hx) as (Y0 & -> & HY).
      simpl in R.
      assert (s1 : seq (Ga ++ D1) Y0).
      { exact (IH X ltac:(simpl; lia) Ga (X :: D1) D1 Y0 X (ext_refl X) Ea R
                  (Permutation_refl _)). }
      assert (s2 : seq ((Ga ++ D1) ++ Gb) C0).
      { exact (IH Y0 ltac:(simpl; lia) (Ga ++ D1) (Y :: Gb) Gb C0 Y HY s1 Eb
                  (Permutation_refl _)). }
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
    + subst A'. destruct (ext_plus_inv _ _ _ Hx)
        as [(P0 & Q0 & -> & HP & HQ) | (-> & HAX)].
      * simpl in R. destruct R as [DP | DQ].
        -- exact (exchange (Permutation_app_head _ Hp)
                    (IH P0 ltac:(simpl; lia) D1 (X :: G) G C0 X HP DP E1
                        (Permutation_refl _))).
        -- exact (exchange (Permutation_app_head _ Hp)
                    (IH Q0 ltac:(simpl; lia) D1 (Y :: G) G C0 Y HQ DQ E2
                        (Permutation_refl _))).
      * (* A' = X ⊕ 1 lewat ext_inl: lanjut ke cabang kiri *)
        exact (IH1 X D2 HAX (perm_skip X Hp)).
    + specialize (IH1 A' (X :: l1 ++ l2) Hx
                      (Permutation_sym (Permutation_middle (X :: l1) _ _))).
      specialize (IH2 A' (Y :: l1 ++ l2) Hx
                      (Permutation_sym (Permutation_middle (Y :: l1) _ _))).
      apply (exchange (perm_front [Plus X Y] D1 _ D2 Hp)).
      apply plus_L.
      * exact (exchange (perm_to_front [X] D1 _) IH1).
      * exact (exchange (perm_to_front [Y] D1 _) IH2).
  - (* submit *)
    exact (submit k (IHE A' D2 Hx H)).
  - (* await *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'. destruct (ext_dia_inv _ _ _ Hx) as (Y0 & -> & HY).
      simpl in R. destruct R as [DY | (k1 & j1 & X1 & Dl & Hk & -> & Hcut)].
      * (* submit terhadap await *)
        assert (s : seq (D1 ++ G) (Dia j C0)).
        { exact (IH Y0 ltac:(simpl; lia) D1 (X :: G) G (Dia j C0) X HY DY E'
                    (Permutation_refl _)). }
        apply (exchange (Permutation_app_head _ Hp)).
        exact (dia_mono _ _ s j C0 (k + j) eq_refl ltac:(lia)).
      * (* await terhadap await: komutasi ke premis derivasi kiri *)
        assert (s : seq ((X1 :: Dl) ++ G) (Dia (j1 + j) C0)).
        { exact (Hcut (Dia j1 X :: G) (Dia (j1 + j) C0) (Dia j1 X) G
                      (ext_dia _ _ _ HY) (await j1 E') (Permutation_refl _)). }
        rewrite Hk, <- Nat.add_assoc.
        exact (exchange (perm_skip _ (Permutation_app_head _ Hp)) (await k1 s)).
    + specialize (IHE A' (X :: l1 ++ l2) Hx
                      (Permutation_sym (Permutation_middle (X :: l1) _ _))).
      apply (exchange (perm_front [Dia k X] D1 _ D2 Hp)).
      apply await.
      exact (exchange (perm_to_front [X] D1 _) IHE).
  - (* cancel *)
    destruct (perm_cons_split _ _ _ _ H) as [[Heq Hp] | (l1 & l2 & -> & Hp)].
    + subst A'.
      exact (IHE _ D2 (ext_cancel_step _ _ _ _ Hx) (perm_skip _ Hp)).
    + specialize (IHE A' (Dia k (Tensor Rr (Plus Xx One)) :: l1 ++ l2) Hx
                      (Permutation_sym
                         (Permutation_middle (Dia k (Tensor Rr (Plus Xx One)) :: l1) _ _))).
      apply (exchange (perm_front [Dia k (Tensor Rr Xx)] D1 _ D2 Hp)).
      apply cancel.
      exact (exchange (perm_to_front [Dia k (Tensor Rr (Plus Xx One))] D1 _) IHE).
Qed.

(** ** Induksi pada derivasi kiri dan pada ukuran formula *)

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
      | Dl k Rr Xx A0 Dd' IHD ];
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
      * intros B Hlt. apply IHn. lia.
      * exists Dl1, Dl2. auto.
    + (* tensor_L *)
      exact (tensor_L (IHD Hs G0 D2 C0 A' Hx E H)).
    + (* lolli_R *)
      refine (cut_E (Lolli X Y) Dl _ Dd' (lolli_R Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. lia.
    + (* lolli_L *)
      simpl. rewrite <- app_assoc.
      exact (lolli_L Da (IHb Hs G0 D2 C0 A' Hx E H)).
    + (* plus_R1 *)
      refine (cut_E (Plus X Y) Dl _ (or_introl Dd') (plus_R1 Y Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. lia.
    + (* plus_R2 *)
      refine (cut_E (Plus X Y) Dl _ (or_intror Dd') (plus_R2 X Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. lia.
    + (* plus_L *)
      exact (plus_L (IH1 Hs G0 D2 C0 A' Hx E H) (IH2 Hs G0 D2 C0 A' Hx E H)).
    + (* submit *)
      refine (cut_E (Dia k X) Dl _ (or_introl Dd') (submit k Dd') G0 C0 E A' D2 Hx H).
      intros B Hlt. apply IHn. lia.
    + (* await *)
      refine (cut_E (Dia (k + j) A0) (Dia k X :: Dl) _ _ (await k Dd')
                G0 C0 E A' D2 Hx H).
      * intros B Hlt. apply IHn. lia.
      * right. exists k, j, X, Dl. split; [reflexivity | split; [reflexivity |]].
        intros G1 C1 A1 D3 Hx1 E1 H1. exact (IHD Hs G1 D3 C1 A1 Hx1 E1 H1).
    + (* cancel *)
      exact (cancel (IHD Hs G0 D2 C0 A' Hx E H)).
Qed.

Theorem cut_admissible : forall A, cut_stmt A.
Proof. intro A. exact (cut_aux (size A) A (le_n _)). Qed.

(** Bentuk biasa: formula cut di kepala konteks kanan. *)
Corollary cut : forall D1 D2 A C,
  seq D1 A -> seq (A :: D2) C -> seq (D1 ++ D2) C.
Proof.
  intros D1 D2 A C Dd E.
  exact (cut_admissible A D1 (A :: D2) D2 C A (ext_refl A) Dd E (Permutation_refl _)).
Qed.
