
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
symbol dbcongT {i j : DBId} (f : DBId → Term) : DBEq i j → TEq (f i) (f j);
rule teq_inv (TRefl $t) ↪ TRefl $t
with teq_trans (TRefl $t) (TRefl _) ↪ TRefl $t
with JtT (TRefl _) (TRefl _) $d ↪ $d
with @Jt _ _ _ _ $T $eqt $d ↪ JtT $eqt (TRefl $T) $d
with @JT _ _ $t _ _ $eqT $d ↪ JtT (TRefl $t) $eqT $d
with @Jcong $t _ $f (TRefl _) ↪ TRefl ($f $t)
with Jeq (TRefl _) (TRefl _) (TRefl _) $d ↪ $d
with dbcongT $f (DBRefl $i) ↪ TRefl ($f $i);

// Congruence for term equality
symbol Jabs {A1 A2 B1 B2 t1 t2 : Term}
            : TEq A1 A2
            → TEq B1 B2
            → TEq t1 t2
            → TEq (tabs A1 B1 t1) (tabs A2 B2 t2);
symbol Japp {A1 A2 B1 B2 f1 f2 a1 a2 : Term}
            : TEq A1 A2
            → TEq B1 B2
            → TEq f1 f2
            → TEq a1 a2
            → TEq (tapp A1 B1 f1 a1) (tapp A2 B2 f2 a2);
symbol Jfun {A1 A2 B1 B2 : Term}
            : TEq A1 A2
            → TEq B1 B2
            → TEq (tfun A1 B1) (tfun A2 B2);
symbol Jpair {A1 A2 B1 B2 a1 a2 b1 b2 : Term}
             : TEq A1 A2
             → TEq B1 B2
             → TEq a1 a2
             → TEq b1 b2
             → TEq (tpair A1 B1 a1 b1) (tpair A2 B2 a2 b2);
symbol Jπ1 {A1 A2 B1 B2 p1 p2 : Term}
           : TEq A1 A2
           → TEq B1 B2
           → TEq p1 p2
           → TEq (π1 A1 B1 p1) (π1 A2 B2 p2);
symbol Jπ2 {A1 A2 B1 B2 p1 p2 : Term}
           : TEq A1 A2
           → TEq B1 B2
           → TEq p1 p2
           → TEq (π2 A1 B1 p1) (π2 A2 B2 p2);
symbol Jsum {A1 A2 B1 B2 : Term}
            : TEq A1 A2
            → TEq B1 B2
            → TEq (tsum A1 B1) (tsum A2 B2);
symbol Jrefl {A1 A2 a1 a2 : Term}
           : TEq A1 A2
           → TEq a1 a2
           → TEq (trefl A1 a1) (trefl A2 a2);
symbol Jteq {A1 A2 a1 a2 b1 b2 : Term}
            : TEq A1 A2
            → TEq a1 a2
            → TEq b1 b2
            → TEq (teq A1 a1 b1) (teq A2 a2 b2);

rule Jabs (TRefl $A) (TRefl $B) (TRefl $t) ↪ TRefl (tabs $A $B $t)
with Japp (TRefl $A) (TRefl $B) (TRefl $f) (TRefl $a) ↪ TRefl (tapp $A $B $f $a)
with Jfun (TRefl $A) (TRefl $B) ↪ TRefl (tfun $A $B)
with Jpair (TRefl $A) (TRefl $B) (TRefl $a) (TRefl $b) ↪ TRefl (tpair $A $B $a $b)
with Jπ1 (TRefl $A) (TRefl $B) (TRefl $p) ↪ TRefl (π1 $A $B $p)
with Jπ2 (TRefl $A) (TRefl $B) (TRefl $p) ↪ TRefl (π2 $A $B $p)
with Jsum (TRefl $A) (TRefl $B) ↪ TRefl (tsum $A $B)
with Jrefl (TRefl $A) (TRefl $a) ↪ TRefl (trefl $A $a)
with Jteq (TRefl $A) (TRefl $a) (TRefl $b) ↪ TRefl (teq $A $a $b);

// Auxiliary lemmas
// dbselect_spec_lt
symbol aux_dbselect_spec_lt (i j : DBId) (eqT gtT ltT : Term) :
  DBLe (dbsucc i) j → TEq (dbselect i j eqT gtT ltT) ltT;
rule aux_dbselect_spec_lt db0 (dbsucc _) _ _ $ltT _ ↪ TRefl $ltT
with aux_dbselect_spec_lt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
   ↪ aux_dbselect_spec_lt $i $j $eqT $gtT $ltT (dble_S_n $h);

// dbselect_spec_gt
symbol aux_dbselect_spec_gt (i j : DBId) (eqT gtT ltT : Term) :
  DBLe (dbsucc j) i → TEq (dbselect i j eqT gtT ltT) gtT;
rule aux_dbselect_spec_gt (dbsucc _) db0 _ $gtT _ _ ↪ TRefl $gtT
with aux_dbselect_spec_gt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
  ↪ aux_dbselect_spec_gt $i $j $eqT $gtT $ltT (dble_S_n $h);

// teq_shift_shift
symbol aux_teq_shift_shift (i j : DBId) (u : Term) :
  DBLe i j → TEq (shift i (shift j u)) (shift (dbsucc j) (shift i u));
symbol aux_teq_shift_shift_var (i j n : DBId) :
  DBLe i j → DBEq (dbshift i (dbshift j n)) (dbshift (dbsucc j) (dbshift i n));

rule aux_teq_shift_shift_var db0 $j $n _ ↪ DBRefl (dbsucc (dbshift $j $n))
with aux_teq_shift_shift_var (dbsucc _) (dbsucc _) db0 _ ↪ DBRefl db0
with aux_teq_shift_shift_var (dbsucc $i) (dbsucc $j) (dbsucc $n) $h
  ↪ dbcongI dbsucc (aux_teq_shift_shift_var $i $j $n (dble_S_n $h))
with aux_teq_shift_shift $i $j (var $n) $h ↪ dbcongT var (aux_teq_shift_shift_var $i $j $n $h)
with aux_teq_shift_shift _ _ (tabs $A $B $t) $h
  ↪ Jabs (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
          (aux_teq_shift_shift _ _ $t (dble_n_S $h))
with aux_teq_shift_shift _ _ (tapp $A $B $f $a) $h
  ↪ Japp (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
          (aux_teq_shift_shift _ _ $f $h)
          (aux_teq_shift_shift _ _ $a $h)
with aux_teq_shift_shift _ _ (tfun $A $B) $h
  ↪ Jfun (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
with aux_teq_shift_shift _ _ (tsort $s) _ ↪ TRefl (tsort $s)
with aux_teq_shift_shift _ _ (tpair $A $B $a $b) $h
  ↪ Jpair (aux_teq_shift_shift _ _ $A $h)
           (aux_teq_shift_shift _ _ $B (dble_n_S $h))
           (aux_teq_shift_shift _ _ $a $h)
           (aux_teq_shift_shift _ _ $b $h)
with aux_teq_shift_shift _ _ (π1 $A $B $p) $h
  ↪ Jπ1 (aux_teq_shift_shift _ _ $A $h)
         (aux_teq_shift_shift _ _ $B (dble_n_S $h))
         (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (π2 $A $B $p) $h
  ↪ Jπ2 (aux_teq_shift_shift _ _ $A $h)
         (aux_teq_shift_shift _ _ $B (dble_n_S $h))
         (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (tsum $A $B) $h
  ↪ Jsum (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
with aux_teq_shift_shift _ _ (trefl $A $a) $h
  ↪ Jrefl (aux_teq_shift_shift _ _ $A $h)
           (aux_teq_shift_shift _ _ $a $h)
with aux_teq_shift_shift _ _ (teq $A $a $b) $h
  ↪ Jteq (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $a $h)
          (aux_teq_shift_shift _ _ $b $h)
;

// TODO teq_shift_shift0
symbol aux_teq_shift_shift0 (i j : DBId) (u : Term) :
  DBLe i j → TEq (Shift (shift j u)) (shift (dbsucc j) (Shift u));

// TODO teq_shift_dbselect
symbol aux_teq_shift_dbselect (n i j : DBId) (eqT gtT ltT : Term) :
  TEq (shift n (dbselect i j eqT gtT ltT))
      (dbselect i j (shift n eqT) (shift n gtT) (shift n ltT));

// TODO teq_shift_dbselect0
symbol aux_teq_shift_dbselect0 (i j : DBId) (eqT gtT ltT : Term) :
  TEq (Shift (dbselect i j eqT gtT ltT))
      (dbselect i j (Shift eqT) (Shift gtT) (Shift ltT));

// TODO teq_dbselect_Sn
symbol aux_teq_dbselect_Sn (i n : DBId) (eqT gtT : Term) :
  TEq (dbselect i n eqT gtT (var n))
      (dbselect i n eqT gtT (var (dbsucc (dbprev n))));

// TODO teq_subst_shift
symbol aux_teq_subst_shift (i j : DBId) (u t : Term) :
  DBLe i j
  → TEq (subst (dbsucc i) (shift j (Shift* j u)) (shift j t))
        (shift j (subst i (Shift* j u) t));

// TODO teq_subst_shift
symbol teq_subst_shift (i : DBId) (u t : Term) :
  TEq (subst (dbsucc i) (Shift u) (Shift t))
      (Shift (subst i u t));

// TODO teq_subst_shift1
symbol teq_subst_shift1 (i : DBId) (u t : Term) :
  TEq (subst (dbsucc (dbsucc i)) (Shift (Shift u)) (Shift1 t))
      (Shift1 (subst (dbsucc i) (Shift u) t));

// TODO teq_select_shift
symbol teq_select_shift (i id : DBId) (V : Term) :
  TEq (dbselect (dbsucc i) (dbsucc id) (Shift V) (var (dbsucc id)) (var id))
      (Shift (dbselect i id V (var id) (var (dbprev id))));

// TODO teq_subst_dbselect
symbol aux_teq_subst_dbselect (i j  k : DBId) (u eqT gtT ltT : Term) :
  TEq (subst k u (dbselect i j eqT gtT ltT))
      (dbselect i j (subst k u eqT) (subst k u gtT) (subst k u ltT));

// TODO dbshift_spec ?

// TODO teq_shift_cancel_subst
symbol aux_teq_shift_cancel_subst (i : DBId) (u t : Term) :
  TEq (subst i u (shift i t)) t;

// TODO teq_subst_subst
symbol aux_teq_subst_subst (i j : DBId) (u t1 t2 : Term) :
  DBLe j i
  → TEq (subst i (Shift* i u) (subst j (Shift* j t1) t2))
        (subst j (subst i (Shift* i u) (Shift* j t1)) (subst (dbsucc i) (Shift* (dbsucc i) u) t2));

// TODO teq_subst_apply
symbol teq_subst_apply (i : DBId) (u t1 t2 : Term) :
  TEq (subst i (Shift* i u) (apply1 t2 t1))
      (apply1 (subst (dbsucc i) (Shift* (dbsucc i) u) t2) (subst i (Shift* i u) t1));

// TODO teq_shift_cancel_subst
symbol teq_shift_cancel_subst (i : DBId) (u t : Term) :
  TEq (subst i u (shift (dbsucc i) (shift i t)))
      (shift i t);