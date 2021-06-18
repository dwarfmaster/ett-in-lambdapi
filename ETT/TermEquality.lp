
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;

// Term equality, necessary to express commutation of different operations
constant symbol TEq : Term → Term → TYPE;
constant symbol TRefl (t : Term) : TEq t t;

// Elimination of term equality
symbol teq_inv {t1 t2 : Term} : TEq t1 t2 → TEq t2 t1;
symbol teq_trans {t1 t2 t3 : Term} : TEq t1 t2 → TEq t2 t3 → TEq t1 t3;
symbol Jt {Γ : Context} {s : Sort} {t1 t2 T : Term}
          : TEq t1 t2 → der Γ t1 T s → der Γ t2 T s;
symbol JT {Γ : Context} {s : Sort} {t T1 T2 : Term}
          : TEq T1 T2 → der Γ t T1 s → der Γ t T2 s;
symbol JtT {Γ : Context} {s : Sort} {t1 t2 T1 T2 : Term}
           : TEq t1 t2 → TEq T1 T2 → der Γ t1 T1 s → der Γ t2 T2 s;
symbol Jcong {t1 t2 : Term} (f : Term → Term)
             : TEq t1 t2 → TEq (f t1) (f t2);
symbol Jeq {Γ : Context} {s : Sort} {T T' t1 t1' t2 t2'}
           : TEq T T'
           → TEq t1 t1'
           → TEq t2 t2'
           → der_eq Γ s T  t1  t2
           → der_eq Γ s T' t1' t2';
rule teq_inv (TRefl $t) ↪ TRefl $t
with teq_trans (TRefl $t) (TRefl _) ↪ TRefl $t
with JtT (TRefl _) (TRefl _) $d ↪ $d
with @Jt _ _ _ _ $T $eqt $d ↪ JtT $eqt (TRefl $T) $d
with @JT _ _ $t _ _ $eqT $d ↪ JtT (TRefl $t) $eqT $d
with @Jcong $t _ $f (TRefl _) ↪ TRefl ($f $t)
with Jeq (TRefl _) (TRefl _) (TRefl _) $d ↪ $d;

// Some equalities
// TODO teq_subst_apply
symbol teq_subst_apply (i : DBId) (u t1 t2 : Term) :
  TEq (subst i (Shift* i u) (apply1 t2 t1))
      (apply1 (subst (dbsucc i) (Shift* (dbsucc i) u) t2) (subst i (Shift* i u) t1));
// TODO teq_subst_shift
symbol teq_subst_shift (i : DBId) (u t : Term) :
  TEq (subst (dbsucc i) (Shift u) (Shift t))
      (Shift (subst i u t));
// TODO teq_subst_shift1
symbol teq_subst_shift1 (i : DBId) (u t : Term) :
  TEq (subst (dbsucc (dbsucc i)) (Shift (Shift u)) (Shift1 t))
      (Shift1 (subst (dbsucc i) (Shift u) t));
// TODO teq_shift_cancel_subst
symbol teq_shift_cancel_subst (i : DBId) (u t : Term) :
  TEq (subst i u (shift (dbsucc i) (shift i t)))
      (shift i t);
// TODO teq_select_shift
symbol teq_select_shift (i id : DBId) (V : Term) :
  TEq (dbselect (dbsucc i) (dbsucc id) (Shift V) (var (dbsucc id)) (var id))
      (Shift (dbselect i id V (var id) (var (dbprev id))));
