
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

