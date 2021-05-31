
require open ETT.XAst;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require ETT.ITT as ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.TranslationDefinition;
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
// TODO der_eq_shift_n
symbol der_eq_shift_n {Γ : Context} {sa s : Sort} {A T t1 t2 : Term} (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tsort sa) (snext sa))
                      (deq : der_eq (sc_to_ctx sc) s T t1 t2)
                      : der_eq (sc_to_sctx dA sc) s (shift id T) (shift id t1) (shift id t2);
symbol der_context_shift_n {Γ : Context} {sa : Sort} {A : Term} (id i : DBId)
                           (sc : ShiftContext Γ id) (dA : der Γ A (tsort sa) (snext sa))
                           : der (sc_to_sctx dA sc) (var (dbshift id i)) (shift id (ShiftN i (get (sc_to_ctx sc) i))) (getS (sc_to_ctx sc) i);

rule sc_to_dsctx $d (SC0 $dΓ) ↪ der_context_push _ _ _ $d $dΓ
with sc_to_dsctx $d (SCSucc $sc $dA) ↪ der_context_push _ _ _ (der_shift_n _ $sc $d $dA) (sc_to_dsctx $d $sc);

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
with der_context_shift_n db0 $i (SC0 $dΓ) $d
  ↪ der_var _ (dbsucc $i) (der_context_push _ _ _ $d $dΓ)
with der_context_shift_n (dbsucc _) db0 (SCSucc $sc $dA) $d
  ↪ der_var _ db0 (sc_to_dsctx $d (SCSucc $sc $dA))
with der_context_shift_n (dbsucc $id) (dbsucc $i) (SCSucc $sc $dA) $d
  ↪ der_shift0 (der_shift_n _ $sc $d $dA) (der_context_shift_n $id $i $sc $d)
;

// Implementation of der_shift{0,1}
rule der_shift0 $dA $dt ↪ der_shift_n db0 (SC0 (inv_context $dA)) $dA $dt
with der_shift1 $dA $dt ↪ der_shift_n db1 (SCSucc (SC0 (inv_context $dA)) (der_getΓ db0 (inv_context $dt))) $dA $dt;

// Compatibility of translation with shifting
// TODO τ_shift0T_eq
// TODO τ_shift0_eq
