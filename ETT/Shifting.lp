
require open ETT.XAst;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require ETT.ITT as ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.Packing;
require open ETT.Congruences;
require open ETT.TranslationDefinition;
require open ETT.TContext;
require open ETT.TranslationLemmas;
require open ETT.Translation;

// Generic der_shift
constant symbol ShiftContext : Context → DBId → TYPE;
symbol sc_to_ctx {Γ : Context} {id : DBId} : ShiftContext Γ id → Context;
symbol sc_to_sctx {Γ : Context} {id : DBId} {s : Sort} {A : Term} : der Γ A (tsort s) (snext s) → ShiftContext Γ id → Context;
symbol sc_to_dctx {Γ : Context} {id : DBId} (sc : ShiftContext Γ id) : der_context (sc_to_ctx sc);
symbol sc_to_dsctx {Γ : Context} {id : DBId} {s : Sort} {A : Term} (dA : der Γ A (tsort s) (snext s)) (sc : ShiftContext Γ id) : der_context (sc_to_sctx dA sc);
constant symbol SC0 {Γ : Context} : der_context Γ → ShiftContext Γ db0;
constant symbol SCSucc {Γ : Context} {s : Sort} {A : Term} {id : DBId} (sc : ShiftContext Γ id) : der (sc_to_ctx sc) A (tsort s) (snext s) → ShiftContext Γ (dbsucc id);
rule sc_to_ctx (@SC0 $Γ _) ↪ $Γ
with sc_to_ctx (@SCSucc _ $s $A _ $sc _) ↪ Push $A $s (sc_to_ctx $sc)
with @sc_to_sctx _ _ $sa $A _ (@SC0 $Γ _) ↪ Push $A $sa $Γ
with sc_to_sctx $d (@SCSucc _ $s $A $id $sc _) ↪ Push (shift $id $A) $s (sc_to_sctx $d $sc);
rule sc_to_dctx (SC0 $dΓ) ↪ $dΓ
with sc_to_dctx (SCSucc $sc $d) ↪ der_context_push _ _ _ $d (sc_to_dctx $sc);
symbol der_shift_n {Γ : Context} {sa s : Sort} {A t T : Term} (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tsort sa) (snext sa))
                   (d : der (sc_to_ctx sc) t T s)
                   : der (sc_to_sctx dA sc) (shift id t) (shift id T) s;
symbol der_eq_shift_n {Γ : Context} {sa s : Sort} {A T t1 t2 : Term} (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tsort sa) (snext sa))
                      (deq : der_eq (sc_to_ctx sc) s T t1 t2)
                      : der_eq (sc_to_sctx dA sc) s (shift id T) (shift id t1) (shift id t2);
symbol der_context_shift_n {Γ : Context} {sa : Sort} {A : Term} (id i : DBId)
                           (sc : ShiftContext Γ id) (dA : der Γ A (tsort sa) (snext sa))
                           : der (sc_to_sctx dA sc) (var (dbshift id i)) (shift id (ShiftN i (get (sc_to_ctx sc) i))) (getS (sc_to_ctx sc) i);

rule sc_to_dsctx $d (SC0 $dΓ) ↪ der_context_push _ _ _ $d $dΓ
with sc_to_dsctx $d (SCSucc $sc $dA) ↪ der_context_push _ _ _ (der_shift_n _ $sc $d $dA) (sc_to_dsctx $d $sc);

// der_shift_n
rule der_shift_n _   $sc $d (der_sort _ $s _) ↪ der_sort _ $s (sc_to_dsctx $d $sc)
with der_shift_n $id $sc $d (der_prod _ $s $s' $A $B $dA $dB) ↪ der_prod _ $s $s' (shift $id $A) (shift (dbsucc $id) $B)
                                                                          (der_shift_n $id $sc $d $dA)
                                                                          (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
with der_shift_n $id $sc $d (der_sigma _ $s $s' $A $B $dA $dB) ↪ der_sigma _ $s $s' (shift $id $A) (shift (dbsucc $id) $B)
                                                                            (der_shift_n $id $sc $d $dA)
                                                                            (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
with der_shift_n $id $sc $d (der_prop_type_eq _ $s $A $u $v $dA $du $dv)
  ↪ der_prop_type_eq _ $s (shift $id $A) (shift $id $u) (shift $id $v)
                      (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du) (der_shift_n $id $sc $d $dv)
with der_shift_n $id $sc $d (der_var _ $i _)
  ↪ der_context_shift_n $id $i $sc $d
with der_shift_n $id $sc $d (der_type_conv _ $u $A $B $s $du $deq)
  ↪ der_type_conv _ (shift $id $u) (shift $id $A) (shift $id $B) $s
                   (der_shift_n $id $sc $d $du) (der_eq_shift_n $id $sc $d $deq)
with der_shift_n $id $sc $d (der_abs _ $s $s' $A $t $B $dA $dB $dt)
  ↪ der_abs _ $s $s' (shift $id $A) (shift (dbsucc $id) $t) (shift (dbsucc $id) $B)
             (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
             (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dt)
with der_shift_n $id $sc $d (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du)
  ↪ der_app _ $s $s' (shift $id $A) (shift $id $t) (shift $id $u) (shift (dbsucc $id) $B)
             (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
             (der_shift_n $id $sc $d $dt) (der_shift_n $id $sc $d $du)
with der_shift_n $id $sc $d (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_pair _ $s $s' (shift $id $u) (shift $id $A) (shift $id $v) (shift (dbsucc $id) $B)
              (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
              (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB) (der_shift_n $id $sc $d $dv)
with der_shift_n $id $sc $d (der_π1 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ der_π1 _ $s $s' (shift $id $p) (shift $id $A) (shift (dbsucc $id) $B)
            (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
            (der_shift_n $id $sc $d $dp)
with der_shift_n $id $sc $d (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ der_π2 _ $s $s' (shift $id $p) (shift $id $A) (shift (dbsucc $id) $B)
            (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
            (der_shift_n $id $sc $d $dp)
with der_shift_n $id $sc $d (der_refl _ $s $u $A $dA $du)
  ↪ der_refl _ $s (shift $id $u) (shift $id $A)
              (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
// der_context_shift_n
with der_context_shift_n db0 $i (SC0 $dΓ) $d
  ↪ der_var _ (dbsucc $i) (der_context_push _ _ _ $d $dΓ)
with der_context_shift_n (dbsucc _) db0 (SCSucc $sc $dA) $d
  ↪ der_var _ db0 (sc_to_dsctx $d (SCSucc $sc $dA))
with der_context_shift_n (dbsucc $id) (dbsucc $i) (SCSucc $sc $dA) $d
  ↪ der_shift0 (der_shift_n _ $sc $d $dA) (der_context_shift_n $id $i $sc $d)
// der_eq_shift_n
with der_eq_shift_n $id $sc $d (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du)
  ↪ der_eq_beta _ $s $s' (shift $id $u) (shift $id $A) (shift (dbsucc $id) $t) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
       (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dt) (der_shift_n $id $sc $d $du)
with der_eq_shift_n $id $sc $d (der_eq_eta _ $s $s' $A $f $B $dA $dB $df)
  ↪ der_eq_eta _ $s $s' (shift $id $A) (shift $id $f) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
       (der_shift_n $id $sc $d $df)
with der_eq_shift_n $id $sc $d (der_eq_π1 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π1 _ $s $s' (shift $id $u) (shift $id $A) (shift $id $v) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
       (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB) (der_shift_n $id $sc $d $dv)
with der_eq_shift_n $id $sc $d (der_eq_π2 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π2 _ $s $s' (shift $id $u) (shift $id $A) (shift $id $v) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
       (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB) (der_shift_n $id $sc $d $dv)
with der_eq_shift_n $id $sc $d (der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deqt $deqT)
  ↪ der_eq_conversion _ $s (shift $id $t1) (shift $id $t2) (shift $id $T1) (shift $id $T2)
       (der_eq_shift_n $id $sc $d $deqt) (der_eq_shift_n $id $sc $d $deqT)
with der_eq_shift_n $id $sc $d (der_eq_lift _ $s $e $u $v $A $de)
  ↪ der_eq_lift _ $s (shift $id $e) (shift $id $u) (shift $id $v) (shift $id $A)
       (der_shift_n $id $sc $d $de)
with der_eq_shift_n $id $sc $d (der_eq_refl _ $s $u $A $du)
  ↪ der_eq_refl _ $s (shift $id $u) (shift $id $A) (der_shift_n $id $sc $d $du)
with der_eq_shift_n $id $sc $d (der_eq_trans _ $s $u $v $w $A $duv $dvw)
  ↪ der_eq_trans _ $s (shift $id $u) (shift $id $v) (shift $id $w) (shift $id $A)
       (der_eq_shift_n $id $sc $d $duv) (der_eq_shift_n $id $sc $d $dvw)
with der_eq_shift_n $id $sc $d (der_eq_symm _ $s $u $v $A $deq)
  ↪ der_eq_symm _ $s (shift $id $u) (shift $id $v) (shift $id $A) (der_eq_shift_n $id $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_tfun _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tfun _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqB)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dB2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tabs _ $s $s' $A1 $A2 $B1 $B2 $t1 $t2 $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ der_eq_cong_tabs _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2) (shift (dbsucc $id) $t1) (shift (dbsucc $id) $t2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqB)
       (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqt)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dB2)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dt1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dt2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tapp _ $s $s' $A1 $A2 $B1 $B2 $f1 $f2 $a1 $a2 $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
  ↪ der_eq_cong_tapp _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
                               (shift $id $f1) (shift $id $f2) (shift $id $a1) (shift $id $a2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqf) (der_eq_shift_n _ $sc $d $deqa)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $df1) (der_shift_n _ $sc $d $df2) (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tsum _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tsum _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqB)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dB2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tpair _ $s $s' $A1 $A2 $B1 $B2 $a1 $a2 $b1 $b2 $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_tpair _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
                                (shift $id $a1) (shift $id $a2) (shift $id $b1) (shift $id $b2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqa) (der_eq_shift_n _ $sc $d $deqb)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2) (der_shift_n _ $sc $d $db1) (der_shift_n _ $sc $d $db2)
with der_eq_shift_n $id $sc $d (der_eq_cong_π1 _ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π1 _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqp)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $dp1) (der_shift_n _ $sc $d $dp2)
with der_eq_shift_n $id $sc $d (der_eq_cong_π2 _ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π2 _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqp)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $dp1) (der_shift_n _ $sc $d $dp2)
with der_eq_shift_n $id $sc $d (der_eq_cong_teq _ $s $A1 $A2 $a1 $a2 $b1 $b2 $deqA $deqa $deqb $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_teq _ $s (shift $id $A1) (shift $id $A2) (shift $id $a1) (shift $id $a2) (shift $id $b1) (shift $id $b2)
        (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ $sc $d $deqa) (der_eq_shift_n _ $sc $d $deqb)
        (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2) (der_shift_n _ $sc $d $db1) (der_shift_n _ $sc $d $db2)
with der_eq_shift_n $id $sc $d (der_eq_cong_trefl _ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
  ↪ der_eq_cong_trefl _ $s (shift $id $A1) (shift $id $A2) (shift $id $a1) (shift $id $a2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ $sc $d $deqa)
       (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2)
;

// Implementation of der_shift{0,1}
rule der_shift0 $dA $dt ↪ der_shift_n db0 (SC0 (inv_context $dA)) $dA $dt
with der_shift1 $dA $dB $dt ↪ der_shift_n db1 (SCSucc (SC0 (inv_context $dB)) $dA) $dB $dt;

// Compatibility of translation with shifting
constant symbol ShiftTContext : TContext → DBId → TYPE;
symbol tsc_to_sc {Γ : TContext} {id : DBId} : ShiftTContext Γ id → ShiftContext (τ_Γ Γ) id;
symbol tsc_to_tc {Γ : TContext} {id : DBId} : ShiftTContext Γ id → TContext;
symbol tsc_to_ctx {Γ : TContext} {id : DBId} : ShiftTContext Γ id → Context;
rule tsc_to_ctx $sc ↪ sc_to_ctx (tsc_to_sc $sc)
with τ_Γ (tsc_to_tc $sc) ↪ sc_to_ctx (tsc_to_sc $sc);
symbol tsc_to_stc {Γ : TContext} {id : DBId} {s : Sort} {A : Term}
                  (dA : der (τ_Γ Γ) A (tsort s) (snext s))
                  : ITT.ε _ (τ Γ dA) → ShiftTContext Γ id → TContext;
symbol tsc_to_sctx {Γ : TContext} {id : DBId} {s : Sort} {A : Term}
                   : der (τ_Γ Γ) A (tsort s) (snext s) → ShiftTContext Γ id → Context;
rule tsc_to_sctx $dA $sc ↪ sc_to_sctx $dA (tsc_to_sc $sc)
with τ_Γ (tsc_to_stc $dA _ $sc) ↪ sc_to_sctx $dA (tsc_to_sc $sc);

constant symbol TSC0 (Γ : TContext) : der_context (τ_Γ Γ) → ShiftTContext Γ db0;
constant symbol TSCSucc {Γ : TContext} {s : Sort} {A : Term} {id : DBId}
                        (sc : ShiftTContext Γ id) (dA : der (tsc_to_ctx sc) A (tsort s) (snext s))
                        : ITT.ε _ (τ (tsc_to_tc sc) dA) → ShiftTContext Γ (dbsucc id);
rule tsc_to_sc (TSC0 _ $dΓ) ↪ SC0 $dΓ
with tsc_to_sc (TSCSucc $sc $dA _) ↪ SCSucc (tsc_to_sc $sc) $dA
with tsc_to_tc (TSC0 $Γ _) ↪ $Γ
with tsc_to_tc (TSCSucc $sc $dA $a) ↪ TPush (tsc_to_tc $sc) _ _ $dA $a;

symbol τ_shift_n {Γ : TContext} {s s' : Sort} {t T A : Term} (id : DBId)
                 (sc : ShiftTContext Γ id) (dt : der (tsc_to_ctx sc) t T s)
                 (dA : der (τ_Γ Γ) A (tsort s') (snext s'))
                 (a : ITT.ε _ (τ Γ dA)) :
  H (τ (tsc_to_tc sc) dt)
    (τ (tsc_to_stc dA a sc) (der_shift_n id (tsc_to_sc sc) dA dt));
symbol τ_shiftT_n {Γ : TContext} {s s' : Sort} {T A : Term} (id : DBId)
                  (sc : ShiftTContext Γ id) (dT : der (tsc_to_ctx sc) T (tsort s) (snext s))
                  (dA : der (τ_Γ Γ) A (tsort s') (snext s'))
                  (a : ITT.ε _ (τ Γ dA)) :
  ITT.ε _ (ITT.eq _ (ITT.u (τ_s s))
    (τ (tsc_to_tc sc) dT)
    (τ (tsc_to_stc dA a sc) (der_shift_n id (tsc_to_sc sc) dA dT))) ≔
  heq_to_eq (τ_shift_n id sc dT dA a);
symbol τ_context_shift_n {Γ : TContext} {sa : Sort} {A : Term} (id i : DBId)
                         (sc : ShiftTContext Γ id) (dA : der (τ_Γ Γ) A (tsort sa) (snext sa))
                         (a : ITT.ε _ (τ Γ dA)) :
  H (tgetShift i (tsc_to_tc sc))
    (τ (tsc_to_stc dA a sc) (der_context_shift_n id i (tsc_to_sc sc) dA));

rule tsc_to_stc $d $x (TSC0 $Γ _) ↪ TPush $Γ _ _ $d $x
with tsc_to_stc $d $x (TSCSucc $sc $dA $a)
  ↪ TPush (tsc_to_stc $d $x $sc) _ _
           (der_shift_n _ (tsc_to_sc $sc) $d $dA)
           (transport (τ_shiftT_n _ $sc $dA $d $x) $a);

rule τ_shift0T_eq $Γ $dT $dA $a ↪ τ_shiftT_n db0 (TSC0 $Γ (inv_context $dA)) $dT $dA $a
with τ_shift0_eq $Γ $dt $dA $a ↪ τ_shift_n db0 (TSC0 $Γ (inv_context $dA)) $dt $dA $a;
rule τ_shift1T_eq $Γ $dT $dA $dB $a $b ↪ τ_shiftT_n db1 (TSCSucc (TSC0 $Γ (inv_context $dB)) $dA $a) $dT $dB $b;

// τ_shift_n
rule τ_shift_n _ _ (der_sort _ $s _) _ _
  ↪ heq_refl _ (ITT.u (τ_s $s))
with τ_shift_n $id $sc (der_prod _ $s _ $A _ $dA $dB) $d $x
  ↪ cong_prod
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (der_shift_n $id (tsc_to_sc $sc) $d $dA) a)
               (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB))
       (τ_shift_n $id $sc $dA $d $x)
       (λ p, heq_trans
          (τ_shift_n _ (TSCSucc $sc $dA (projT1 p)) $dB $d $x)
          (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d $dA) (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                              (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc $dA $d $x))) (projHEq p)))
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)))
with τ_shift_n $id $sc (der_sigma _ $s _ $A _ $dA $dB) $d $x
  ↪ cong_sum
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (der_shift_n $id (tsc_to_sc $sc) $d $dA) a)
               (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB))
       (τ_shift_n $id $sc $dA $d $x)
       (λ p, heq_trans
          (τ_shift_n _ (TSCSucc $sc $dA (projT1 p)) $dB $d $x)
          (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d $dA) (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                              (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc $dA $d $x))) (projHEq p)))
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)))
with τ_shift_n $id $sc (der_prop_type_eq _ _ _ _ _ $dA $da1 $da2) $d $x
  ↪ cong_eq
       (τ_shift_n $id $sc $dA $d $x)
       (heq_conj
         (τ_shift_n $id $sc $da1 $d $x)
         (convert_T (tsc_to_tc $sc) (inv_sort $da1) $dA)
         (convert_T (tsc_to_stc $d $x $sc) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $da1)) (der_shift_n $id (tsc_to_sc $sc) $d $dA)))
       (heq_conj
         (τ_shift_n $id $sc $da2 $d $x)
         (convert_T (tsc_to_tc $sc) (inv_sort $da2) $dA)
         (convert_T (tsc_to_stc $d $x $sc) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $da2)) (der_shift_n $id (tsc_to_sc $sc) $d $dA)))
with τ_shift_n $id $sc (der_var _ $i $dΓ) $d $x
  ↪ heq_trans
       (heq_symm (heq_of_transport
         (tgetShift $i (tsc_to_tc $sc))
         (convert_T (tsc_to_tc $sc) (der_shift $i (τ_dΓ (tsc_to_tc $sc)) (tgetD $i (tsc_to_tc $sc))) (der_shift $i $dΓ (der_getΓ $i $dΓ)))))
       (τ_context_shift_n $id $i $sc $d $x)
with τ_shift_n $id $sc (der_type_conv _ _ _ _ _ $du $deq) $d $x
  ↪ heq_conj
       (heq_conj
         (τ_shift_n $id $sc $du $d $x)
         (convert_T (tsc_to_tc $sc) (inv_sort $du) (inv_eq_t1 $deq))
         (convert_T (tsc_to_stc $d $x $sc)
                    (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du))
                    (inv_eq_t1 (der_eq_shift_n $id (tsc_to_sc $sc) $d $deq))))
       (τ_eqT (tsc_to_tc $sc) $deq)
       (τ_eqT (tsc_to_stc $d $x $sc) (der_eq_shift_n $id (tsc_to_sc $sc) $d $deq))
with τ_shift_n $id $sc (der_abs _ $s _ $A _ _ $dA _ $dt) $d $x
  ↪ cong_lambda
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) (inv_sort $dt))
       (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (der_shift_n $id (tsc_to_sc $sc) $d $dA) a)
               (inv_sort (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dt)))
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dt)
       (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (der_shift_n $id (tsc_to_sc $sc) $d $dA) a)
               (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dt))
       (τ_shift_n $id $sc $dA $d $x)
       (λ p, heq_trans
          (τ_shift_n _ (TSCSucc $sc $dA (projT1 p)) (inv_sort $dt) $d $x)
          (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d $dA) (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                              (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc $dA $d $x))) (projHEq p)))
                    (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d (inv_sort $dt))
                    (inv_sort (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dt))))
       (λ p, heq_trans
          (τ_shift_n _ (TSCSucc $sc $dA (projT1 p)) $dt $d $x)
          (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d $dA) (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                              (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc $dA $d $x))) (projHEq p)))
                    (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dt)
                    (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dt)))
with τ_shift_n $id $sc (der_app _ $s _ $A _ _ _ $dA $dB $df $du) $d $x
  ↪ heq_conj
       (cong_app
         (λ a, τ (TPush (tsc_to_tc $sc) $s $A (inv_sort $du) a) $dB)
         (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du)) a)
                 (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB))
         (heq_trans
           (τ_shift_n $id $sc (inv_sort $du) $d $x)
           (convert (tsc_to_stc $d $x $sc) (der_shift_n $id (tsc_to_sc $sc) $d (inv_sort $du)) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du))))
         (λ p, heq_trans
            (τ_shift_n _ (TSCSucc $sc (inv_sort $du) (projT1 p)) $dB $d $x)
            (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d (inv_sort $du)) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du))
                                (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc (inv_sort $du) $d $x))) (projHEq p)))
                      (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) (inv_sort $du)) $d $dB)
                      (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)))
         (heq_conj
           (τ_shift_n $id $sc $df $d $x)
           (τ_fun_eq (tsc_to_tc $sc) (inv_sort $du) $dB (inv_sort $df))
           (τ_fun_eq (tsc_to_stc $d $x $sc)
                     (inv_sort (der_shift_n _ (tsc_to_sc $sc) $d $du))
                     (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                     (inv_sort (der_shift_n _ (tsc_to_sc $sc) $d $df))))
         (τ_shift_n $id $sc $du $d $x))
       (τ_substT_eq (tsc_to_tc $sc) $dB $du)
       (τ_substT_eq (tsc_to_stc $d $x $sc) (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                                           (der_shift_n _ (tsc_to_sc $sc)              $d $du))
with τ_shift_n $id $sc (der_pair _ $s _ _ $A _ _ $dA $du $dB $dv) $d $x
  ↪ cong_pair
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A (inv_sort $du) a) $dB)
       (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du)) a)
               (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dB))
       (heq_trans
         (τ_shift_n $id $sc (inv_sort $du) $d $x)
         (convert (tsc_to_stc $d $x $sc) (der_shift_n $id (tsc_to_sc $sc) $d (inv_sort $du)) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du))))
       (λ p, heq_trans
          (τ_shift_n _ (TSCSucc $sc (inv_sort $du) (projT1 p)) $dB $d $x)
          (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d (inv_sort $du)) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du))
                              (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc (inv_sort $du) $d $x))) (projHEq p)))
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) (inv_sort $du)) $d $dB)
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)))
       (τ_shift_n $id $sc $du $d $x)
       (heq_conj
         (heq_conj
           (τ_shift_n $id $sc $dv $d $x)
           (convert_T (tsc_to_tc $sc) (inv_sort $dv) (substitution $dB $du))
           (convert_T (tsc_to_stc $d $x $sc) (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $dv))
             (substitution (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                           (der_shift_n _ (tsc_to_sc $sc) $d $du))))
         (inv_eq (τ_substT_eq (tsc_to_tc $sc) $dB $du))
         (inv_eq (τ_substT_eq (tsc_to_stc $d $x $sc)
                   (der_shift_n _ (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                   (der_shift_n _ (tsc_to_sc $sc) $d $du))))
with τ_shift_n $id $sc (der_π1 _ $s _ _ $A _ $dA $dB $dp) $d $x
  ↪ cong_proj1
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (der_shift_n $id (tsc_to_sc $sc) $d $dA) a)
               (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB))
       (τ_shift_n $id $sc $dA $d $x)
       (λ p, heq_trans
          (τ_shift_n _ (TSCSucc $sc $dA (projT1 p)) $dB $d $x)
          (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d $dA) (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                              (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc $dA $d $x))) (projHEq p)))
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                    (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)))
       (heq_conj
         (τ_shift_n $id $sc $dp $d $x)
         (τ_sum_eq (tsc_to_tc $sc) $dA $dB (inv_sort $dp))
         (τ_sum_eq (tsc_to_stc $d $x $sc)
                   (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                   (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                   (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $dp))))
with τ_shift_n $id $sc (der_π2 _ $s $s' $p $A $B $dA $dB $dp) $d $x
  ↪ heq_conj
       (cong_proj2
         (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
         (λ a, τ (TPush (tsc_to_stc $d $x $sc) $s (shift $id $A) (der_shift_n $id (tsc_to_sc $sc) $d $dA) a)
                 (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB))
         (τ_shift_n $id $sc $dA $d $x)
         (λ p, heq_trans
            (τ_shift_n _ (TSCSucc $sc $dA (projT1 p)) $dB $d $x)
            (convertR _ (PCPush (PCEmpty (tsc_to_stc $d $x $sc)) (der_shift_n $id (tsc_to_sc $sc) $d $dA) (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                                (heq_trans (heq_symm (heq_of_transport (projT1 p) (τ_shiftT_n _ $sc $dA $d $x))) (projHEq p)))
                      (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                      (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)))
         (heq_conj
           (τ_shift_n $id $sc $dp $d $x)
           (τ_sum_eq (tsc_to_tc $sc) $dA $dB (inv_sort $dp))
           (τ_sum_eq (tsc_to_stc $d $x $sc)
                     (der_shift_n $id (tsc_to_sc $sc) $d $dA)
                     (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
                     (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $dp)))))
       (τ_substT_eq (tsc_to_tc $sc) $dB (der_π1 (tsc_to_ctx $sc) $s $s' $p $A $B $dA $dB $dp))
       (τ_substT_eq (tsc_to_stc $d $x $sc)
         (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
         (der_π1 (tsc_to_sctx $d $sc) $s $s'
           (shift $id $p) (shift $id $A) (shift (dbsucc $id) $B)
           (der_shift_n $id (tsc_to_sc $sc) $d $dA)
           (der_shift_n (dbsucc $id) (SCSucc (tsc_to_sc $sc) $dA) $d $dB)
           (der_shift_n $id (tsc_to_sc $sc) $d $dp)))
with τ_shift_n $id $sc (der_refl _ _ _ _ $dA $du) $d $x
  ↪ cong_refl
       (τ_shift_n $id $sc $dA $d $x)
       (heq_conj
         (τ_shift_n $id $sc $du $d $x)
         (convert_T (tsc_to_tc $sc) (inv_sort $du) $dA)
         (convert_T (tsc_to_stc $d $x $sc)
           (inv_sort (der_shift_n $id (tsc_to_sc $sc) $d $du))
           (der_shift_n $id (tsc_to_sc $sc) $d $dA)))
// τ_context_shift_n
with τ_context_shift_n db0 $i (TSC0 $Γ $dΓ) $d $x
  ↪ heq_trans
       (heq_of_transport
         (tgetShift $i $Γ)
         (τ_shift0T_eq $Γ (der_shift $i (τ_dΓ $Γ) (tgetD $i $Γ)) $d $x))
       (heq_of_transport
         (tgetShift (dbsucc $i) (TPush $Γ _ _ $d $x))
         (convert_T (TPush $Γ _ _ $d $x)
                    (der_shift (dbsucc $i) (τ_dΓ (TPush $Γ _ _ $d $x)) (tgetD (dbsucc $i) (TPush $Γ _ _ $d $x)))
                    (der_shift (dbsucc $i) (der_context_push _ _ _ $d $dΓ) (der_getΓ (dbsucc $i) (der_context_push _ _ _ $d $dΓ)))))
with τ_context_shift_n (dbsucc _) db0 (TSCSucc $sc $dA $a) $d $x
  ↪ heq_trans
       (heq_conj
         (heq_of_transport $a
           (τ_shiftT_n _ $sc $dA $d $x))
         (τ_shift0T_eq (tsc_to_tc $sc) $dA $dA $a)
         (τ_shift0T_eq (tsc_to_stc $d $x $sc)
                       (der_shift_n _ (tsc_to_sc $sc) $d $dA)
                       (der_shift_n _ (tsc_to_sc $sc) $d $dA)
                       (transport (τ_shiftT_n _ $sc $dA $d $x) $a)))
       (heq_of_transport
         (tgetShift db0 (tsc_to_stc $d $x (TSCSucc $sc $dA $a)))
         (convert_T (tsc_to_stc $d $x (TSCSucc $sc $dA $a))
                    (der_shift db0 (τ_dΓ (tsc_to_stc $d $x (TSCSucc $sc $dA $a))) (tgetD db0 (tsc_to_stc $d $x (TSCSucc $sc $dA $a))))
                    (der_shift db0 (sc_to_dsctx $d (SCSucc (tsc_to_sc $sc) $dA)) (der_getΓ db0 (sc_to_dsctx $d (SCSucc (tsc_to_sc $sc) $dA))))))
with τ_context_shift_n (dbsucc $id) (dbsucc $i) (TSCSucc $sc $dA $a) $d $x
  ↪ heq_trans
       (heq_symm (heq_of_transport
         (tgetShift $i (tsc_to_tc $sc))
         (τ_shift0T_eq (tsc_to_tc $sc)
           (der_shift $i (τ_dΓ (tsc_to_tc $sc)) (tgetD $i (tsc_to_tc $sc)))
           $dA $a)))
       (heq_trans
         (τ_context_shift_n $id $i $sc $d $x)
         (τ_shift0_eq (tsc_to_stc $d $x $sc)
           (der_context_shift_n $id $i (tsc_to_sc $sc) $d)
           (der_shift_n _ (tsc_to_sc $sc) $d $dA)
           (transport (τ_shiftT_n _ $sc $dA $d $x) $a)))
;
