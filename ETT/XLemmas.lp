
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;

// Lemmas
symbol der_shift1 (Γ : Context) (t T : Term) (s : Sort) (_ : der (getΓ Γ db0) t T s) : der Γ (Shift t) (Shift T) s;
symbol der_shift (id : DBId) (Γ : Context) (t T : Term) (s : Sort) (_ : der (getΓ Γ id) t T s) : der Γ (ShiftN id t) (ShiftN id T) s;
rule der_shift db0 $Γ $t $T $s $d ↪ der_shift1 $Γ $t $T $s $d
with der_shift (dbsucc $id) $Γ $t $T $s $d ↪ der_shift1 $Γ _ _ _ (der_shift $id _ $t $T $s $d);

symbol der_eq_ctx (Γ : Context) (s s' : Sort) (c C t1 t2 T : Term)
                  (_ : der_eq Γ s T t1 t2) (_ : der (Push T s Γ) c C s')
                  : der_eq Γ s' (apply1 C t1) (apply1 c t1) (apply1 c t2);

symbol der_conv_in_ctx (Γ : Context) (s s' : Sort) (A A' t B : Term)
                       (_ : der_eq Γ (snext s) (tsort s) A A') (_ : der (Push A s Γ) t B s')
                       : der (Push A' s Γ) t B s';

symbol der_extend_context (Γ1 Γ2 : Context) (s : Sort) (t T : Term)
                          (_ : der_context Γ1) (_ : der Γ2 t T s)
                          : der (Append Γ2 Γ1) t T s;
