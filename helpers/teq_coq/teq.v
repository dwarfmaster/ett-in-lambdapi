
Inductive Term : Set :=
| var : nat -> Term
| tabs : Term -> Term -> Term -> Term
| tapp : Term -> Term -> Term -> Term -> Term
| tfun : Term -> Term -> Term
| tsort : nat -> Term
| tpair : Term -> Term -> Term -> Term -> Term
| tp1 : Term -> Term -> Term -> Term
| tp2 : Term -> Term -> Term -> Term
| tsum : Term -> Term -> Term
| trefl : Term -> Term -> Term
| teq : Term -> Term -> Term -> Term
.

Fixpoint dbshift (n m : nat) : nat :=
  match n,m with
  | S n, S m => S (dbshift n m)
  | 0, m => S m
  | S n, 0 => 0
  end.
Definition dbprev (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n => n
  end.

Fixpoint shift (i : nat) (t : Term) : Term :=
  match t with
  | var id => var (dbshift i id)
  | tabs A B t => tabs (shift i A) (shift (S i) B) (shift (S i) t)
  | tapp A B f a => tapp (shift i A) (shift (S i) B) (shift i f) (shift i a)
  | tfun A B => tfun (shift i A) (shift (S i) B)
  | tsort s => tsort s
  | tpair A B a b => tpair (shift i A) (shift (S i) B) (shift i a) (shift i b)
  | tp1 A B p => tp1 (shift i A) (shift (S i) B) (shift i p)
  | tp2 A B p => tp2 (shift i A) (shift (S i) B) (shift i p)
  | tsum A B => tsum (shift i A) (shift (S i) B)
  | trefl A a => trefl (shift i A) (shift i a)
  | teq A a b => teq (shift i A) (shift i a) (shift i b)
  end.
Definition Shift := shift 0.
Definition Shift1 := shift 1.

Fixpoint Shift' (n : nat) (t : Term) : Term :=
  match n with
  | 0 => t
  | S n => Shift (Shift' n t)
  end.
Definition ShiftN (n : nat) : Term -> Term := Shift' (S n).

Fixpoint dbselect (i j : nat) (eq gt lt : Term) : Term :=
  match i, j with
  | 0, 0 => eq
  | S i, S j => dbselect i j eq gt lt
  | 0, S _ => lt
  | S _, 0 => gt
  end.

Fixpoint sub (i : nat) (V t : Term) :=
  match t with
  | var id => dbselect i id V (var id) (var (dbprev id))
  | tabs A B t => tabs (sub i V A) (sub (S i) (Shift V) B) (sub (S i) (Shift V) t)
  | tapp A B f a => tapp (sub i V A) (sub (S i) (Shift V) B) (sub i V f) (sub i V a)
  | tfun A B => tfun (sub i V A) (sub (S i) (Shift V) B)
  | tsort s => tsort s
  | tpair A B a b => tpair (sub i V A) (sub (S i) (Shift V) B) (sub i V a) (sub i V b)
  | tp1 A B p => tp1 (sub i V A) (sub (S i) (Shift V) B) (sub i V p)
  | tp2 A B p => tp2 (sub i V A) (sub (S i) (Shift V) B) (sub i V p)
  | tsum A B => tsum (sub i V A) (sub (S i) (Shift V) B)
  | trefl A a => trefl (sub i V A) (sub i V a)
  | teq A a b => teq (sub i V A) (sub i V a) (sub i V b)
  end.
Definition apply1 (t1 t2 : Term) := sub 0 t2 t1.

Ltac rewrite_all' :=
  match goal with
  | H : _ |- _ => rewrite H by auto; rewrite_all'
  | _ => idtac
  end.
Ltac fold_Shift' :=
  match goal with
  | |- context[Shift (Shift' ?n ?u)]
      => change (Shift (Shift' n u)) with (Shift' (S n) u); fold_Shift'
  | _ => idtac
  end.

Hint Resolve le_n_S : core.
Hint Extern 0 => rewrite_all' : core.

Lemma ordered_integers (i j n : nat) :
  j <= i ->
  n <= j \/ (j < n /\ n <= i) \/ i < n.
Proof.
  intro Hij.
  induction n.
  - destruct j; auto. left. apply le_0_n.
  - destruct Hij; destruct IHn as [ Hnj | [ [ Hjn Hni ] | Hin ] ]; auto.
    + destruct Hnj; auto.
    + destruct Hnj; auto.
    + destruct Hni; auto.
      right. left. split; auto.
Qed.

Lemma dbshift_spec1 (i j : nat) :
  i <= j -> dbshift i j = S j.
Proof.
  generalize dependent i.
  induction j; intros i H; destruct i; auto.
  - inversion H.
  - simpl. f_equal. apply IHj.
    apply le_S_n. assumption.
Qed.

Lemma dbshift_spec2 (i j : nat) :
  j < i -> dbshift i j = j.
Proof.
  generalize dependent i.
  induction j; intros i H; destruct i; auto.
  - inversion H.
  - inversion H.
  - simpl. f_equal. apply IHj.
    unfold lt in *. apply le_S_n. assumption.
Qed.

Lemma dbselect_spec_lt (i j : nat) (eqT gtT ltT : Term) :
  i < j -> dbselect i j eqT gtT ltT = ltT.
Proof.
  generalize dependent i.
  induction j; intros i H; destruct i; simpl; auto.
  - inversion H.
  - inversion H.
  - apply IHj. unfold lt in *. apply le_S_n. assumption.
Qed.

Lemma dbselect_spec_eq (i j : nat) (eqT gtT ltT : Term) :
  i = j -> dbselect i j eqT gtT ltT = eqT.
Proof.
  intro H. subst. induction j; auto.
Qed.

Lemma dbselect_spec_gt (i j : nat) (eqT gtT ltT : Term) :
  i > j -> dbselect i j eqT gtT ltT = gtT.
Proof.
  unfold gt. unfold lt. generalize dependent i.
  induction j; intros i H; destruct i; simpl; auto.
  - inversion H.
  - inversion H.
  - apply IHj. apply le_S_n. assumption.
Qed.

Lemma teq_shift_shift (i j : nat) (u : Term) :
  i <= j -> shift i (shift j u) = shift (S j) (shift i u).
Proof.
  generalize dependent j. generalize dependent i.
  induction u; intros i j H; simpl; auto.
  f_equal. generalize dependent j. generalize dependent i.
  induction n; intros i j Hij; simpl.
  { destruct i; simpl; try reflexivity.
    destruct Hij; simpl; reflexivity.
  }
  { destruct i; destruct j; simpl; auto.
    - inversion Hij.
    - f_equal. apply IHn. apply le_S_n. assumption.
  }
Qed.
Lemma teq_shift_shift0 (i : nat) (u : Term) :
  Shift (shift i u) = shift (S i) (Shift u).
Proof.
  apply teq_shift_shift. apply le_0_n.
Qed.

Lemma teq_shift_dbselect (n i j : nat) (eqT gtT ltT : Term) :
  shift n (dbselect i j eqT gtT ltT) = dbselect i j (shift n eqT) (shift n gtT) (shift n ltT).
Proof.
  generalize dependent j.
  induction i; intro j; destruct j; auto.
  simpl. apply IHi.
Qed.
Lemma teq_shift_dbselect0 (i j : nat) (eqT gtT ltT : Term) :
  Shift (dbselect i j eqT gtT ltT) = dbselect i j (Shift eqT) (Shift gtT) (Shift ltT).
Proof.
  unfold Shift. apply teq_shift_dbselect.
Qed.
Lemma teq_dbselect_Sn (i n : nat) (eqT gtT : Term) :
  dbselect i n eqT gtT (var n) = dbselect i n eqT gtT (var (S (dbprev n))).
Proof.
  induction i; induction n; reflexivity.
Qed.

Ltac raise_dbselect :=
  match goal with
  | |- context[shift ?n (dbselect ?i ?j ?e ?g ?l)]
  (*| |- context[dbselect ?i ?j (shift ?n ?e) (shift ?n ?g) (shift ?n ?l)] *)
      => rewrite -> (teq_shift_dbselect n i j e g l); raise_dbselect
  | |- context[Shift (dbselect ?i ?j ?e ?g ?l)]
      => rewrite -> (teq_shift_dbselect0 i j e g l); raise_dbselect
  | _ => idtac
  end.
Ltac pop_shift :=
  match goal with
  | |- context[dbselect ?i ?j (shift ?n ?e) (shift ?n ?g) (shift ?n ?l)]
      => rewrite <- (teq_shift_dbselect n i j e g l); pop_shift
  | |- context[dbselect ?i ?n ?eqT ?gtT (var ?n)]
      => rewrite -> (teq_dbselect_Sn i n eqT gtT); pop_shift
  | |- context[var (S ?n)]
      => change (var (S n)) with (Shift (var n)); pop_shift
  | |- context[shift (S ?n) (Shift ?u)]
      => rewrite <- (teq_shift_shift0 n u); pop_shift
  | |- context[dbselect ?i ?j (Shift ?e) (Shift ?g) (Shift ?l)]
      => rewrite <- (teq_shift_dbselect0 i j e g l); pop_shift
  | _ => idtac
  end.
Ltac push_shift :=
  match goal with
  | |- context[Shift (dbselect ?i ?j ?eqT ?gtT ?ltT)]
      => rewrite -> (teq_shift_dbselect0 i j eqT gtT ltT); push_shift
  | |- context[Shift (shift ?n ?u)]
      => rewrite -> (teq_shift_shift0 n u); push_shift
  | |- context[Shift (var ?n)]
      => change (Shift (var n)) with (var (S n)); push_shift
  | |- context[dbselect ?i ?n ?eqT ?gtT (var (S (dbprev ?n)))]
      => rewrite <- (teq_dbselect_Sn i n eqT gtT); push_shift
  | _ => idtac
  end.

Lemma teq_subst_shift (i j : nat) (u t : Term) :
  j <= i ->
  sub (S i) (shift j (Shift' j u)) (shift j t) = shift j (sub i (Shift' j u) t).
Proof.
  generalize dependent u.
  generalize dependent j. generalize dependent i.
  induction t; intros i j u Hij; simpl; push_shift; fold_Shift'; auto.
  generalize dependent j. generalize dependent i.
  induction n; intros i j Hij; simpl.
  - destruct i; destruct j; simpl; try reflexivity. inversion Hij.
  - destruct i; destruct j; simpl.
    + reflexivity.
    + inversion Hij.
    + raise_dbselect. reflexivity.
    + remember (dbshift j n) as djn. pose (IH := (IHn i j)). rewrite <- Heqdjn in IH.
      destruct djn; pop_shift; f_equal; push_shift; apply IH; apply le_S_n; assumption.
Qed.

Lemma LP_teq_subst_shift (i : nat) (u t : Term) :
  sub (S i) (Shift u) (Shift t) = Shift (sub i u t).
Proof.
  unfold Shift. change u with (Shift' 0 u).
  apply (teq_subst_shift i 0 u t). apply le_0_n.
Qed.
Lemma LP_teq_subst_shift1 (i : nat) (u t : Term) :
  sub (S (S i)) (Shift (Shift u)) (Shift1 t)
  = Shift1 (sub (S i) (Shift u) t).
Proof.
  unfold Shift. rewrite teq_shift_shift0. unfold Shift.
  change (shift 0 u) with (Shift' 1 u). unfold Shift1.
  apply teq_subst_shift. apply le_n_S. apply le_0_n.
Qed.
Lemma LP_teq_select_shift (i id : nat) (V : Term) :
  dbselect (S i) (S id) (Shift V) (var (S id)) (var id)
  = Shift (dbselect i id V (var id) (var (dbprev id))).
Proof.
  simpl. pop_shift. reflexivity.
Qed.

Ltac pop_shift ::=
  match goal with
  | |- context[dbselect ?i ?j (shift ?n ?e) (shift ?n ?g) (shift ?n ?l)]
      => rewrite <- (teq_shift_dbselect n i j e g l); pop_shift
  | |- context[dbselect ?i ?n ?eqT ?gtT (var ?n)]
      => rewrite -> (teq_dbselect_Sn i n eqT gtT); pop_shift
  | |- context[var (S ?n)]
      => change (var (S n)) with (Shift (var n)); pop_shift
  | |- context[shift (S ?n) (Shift ?u)]
      => rewrite <- (teq_shift_shift0 n u); pop_shift
  | |- context[dbselect ?i ?j (Shift ?e) (Shift ?g) (Shift ?l)]
      => rewrite <- (teq_shift_dbselect0 i j e g l); pop_shift
  | |- context[sub (S ?i) (Shift ?u) (Shift ?t)]
      => rewrite -> (LP_teq_subst_shift i u t); pop_shift
  | _ => idtac
  end.
Ltac push_shift ::=
  match goal with
  | |- context[Shift (sub ?i ?u ?t)]
      => rewrite <- (LP_teq_subst_shift i u t); push_shift
  | |- context[Shift (dbselect ?i ?j ?eqT ?gtT ?ltT)]
      => rewrite -> (teq_shift_dbselect0 i j eqT gtT ltT); push_shift
  | |- context[Shift (shift ?n ?u)]
      => rewrite -> (teq_shift_shift0 n u); push_shift
  | |- context[Shift (var ?n)]
      => change (Shift (var n)) with (var (S n)); push_shift
  | |- context[dbselect ?i ?n ?eqT ?gtT (var (S (dbprev ?n)))]
      => rewrite <- (teq_dbselect_Sn i n eqT gtT); push_shift
  | _ => idtac
  end.

Lemma teq_subst_dbselect (i j k : nat) (u eqT gtT ltT : Term) :
  sub k u (dbselect i j eqT gtT ltT) = dbselect i j (sub k u eqT) (sub k u gtT) (sub k u ltT).
Proof.
  generalize dependent j.
  induction i; intro j; destruct j; simpl; try reflexivity.
  apply IHi.
Qed.

Lemma dbshift_spec (i n : nat) :
  (dbshift i n = n /\ dbshift i n < i)
  \/ (dbshift i n = S n /\ dbshift i n > i).
Proof.
  generalize dependent n. induction i; intro n; simpl.
  - right. split; try reflexivity. unfold gt. unfold lt. apply le_n_S. apply le_0_n.
  - destruct n; simpl.
    + left. split; try reflexivity. unfold lt. apply le_n_S. apply le_0_n.
    + destruct (IHi n) as [ [ Heq H ] | [ Heq H ] ]; [ left | right ];
        rewrite Heq in *; split; try reflexivity;
        unfold gt in *; unfold lt in *; auto using le_n_S.
Qed.

Lemma teq_shift_cancel_subst (i : nat) (u t : Term) :
  sub i u (shift i t) = t.
Proof.
  generalize dependent i. generalize dependent u.
  induction t; simpl; try (intros u i; rewrite_all'; reflexivity).
  induction n; intros u i; destruct i; simpl; try reflexivity.
  pop_shift. destruct (dbshift_spec i n) as [ [ Heq H ] | [ Heq H ] ].
  - rewrite dbselect_spec_gt by (unfold gt; assumption).
    rewrite Heq. reflexivity.
  - push_shift. rewrite dbselect_spec_lt by (unfold gt in H; assumption).
    rewrite Heq. reflexivity.
Qed.

Lemma teq_subst_subst (i j : nat) (u t1 t2 : Term) :
  j <= i ->
  sub i (Shift' i u) (sub j (Shift' j t1) t2)
  = sub j (sub i (Shift' i u) (Shift' j t1)) (sub (S i) (Shift' (S i) u) t2).
Proof.
  generalize dependent t1. generalize dependent u.
  generalize dependent j. generalize dependent i.
  induction t2;
    try (intros i j u t1 Hij; simpl; fold_Shift';
         rewrite_all'; simpl; push_shift; fold_Shift'; reflexivity).
  induction n; intros i j u t1 Hij;
    destruct i; destruct j; simpl; try reflexivity.
  - inversion Hij.
  - destruct n; simpl; try reflexivity. unfold Shift.
    symmetry. change (sub 0 u t1) with (Shift' 0 (sub 0 u t1)).
    apply teq_shift_cancel_subst.
  - inversion Hij.
  - destruct n; simpl; try reflexivity. simpl in IHn.
    pop_shift. unfold Shift.
    change (sub (S i) (shift 0 (Shift' i u)) t1)
      with (Shift' 0 (sub (S i) (shift 0 (Shift' i u)) t1)).
    rewrite teq_shift_cancel_subst. reflexivity.
  - destruct n; simpl; pop_shift; f_equal; simpl in IHn;
      push_shift; apply IHn; apply le_S_n; assumption.
Qed.

Lemma LP_teq_subst_apply (i : nat) (u t1 t2 : Term) :
  sub i (Shift' i u) (apply1 t2 t1)
  = apply1 (sub (S i) (Shift' (S i) u) t2) (sub i (Shift' i u) t1).
Proof.
  unfold apply1. change t1 with (Shift' 0 t1).
  apply teq_subst_subst. apply le_0_n.
Qed.

Lemma LP_teq_shift_cancel_subst (i : nat) (u t : Term) :
  sub i u (shift (S i) (shift i t)) = shift i t.
Proof.
  rewrite <- teq_shift_shift by constructor.
  apply teq_shift_cancel_subst.
Qed.
