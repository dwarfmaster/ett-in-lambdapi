
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;

// Lemmas
// TODO der_shift0
symbol der_shift0 (Γ : Context) {t T : Term} {s : Sort} (_ : der (getΓ Γ db0) t T s) : der Γ (Shift t) (Shift T) s;
// TODO der_shift1
symbol der_shift1 {Γ : Context} {t A T : Term} (B : Term) {s sa : Sort} (sb : Sort) (_ : der (Push A sa Γ) t T s) : der (Push (Shift A) sa (Push B sb Γ)) (Shift1 t) (Shift1 T) s;
symbol der_shift (id : DBId) (Γ : Context) (t T : Term) (s : Sort) (_ : der (getΓ Γ id) t T s) : der Γ (ShiftN id t) (ShiftN id T) s;
rule der_shift db0 $Γ $t $T $s $d ↪ @der_shift0 $Γ $t $T $s $d
with der_shift (dbsucc $id) $Γ $t $T $s $d ↪ der_shift0 $Γ (der_shift $id _ $t $T $s $d);

// TODO remove der_eq_ctx, replace by der_eq_cong_apply
symbol der_eq_ctx (Γ : Context) (s s' : Sort) (c C t1 t2 T : Term)
                  (_ : der_eq Γ s T t1 t2) (_ : der (Push T s Γ) c C s')
                  : der_eq Γ s' (apply1 C t1) (apply1 c t1) (apply1 c t2);

// TODO der_eq_cong_apply
symbol der_eq_cong_apply (Γ : Context) {s s' : Sort} {A1 A2 B1 B2 t1 t2 : Term}
                         (_ : der_eq Γ (snext s) (tsort s) A1 A2) (_ : der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2)
                         (_ : der_eq Γ s A1 t1 t2)
                         (_ : der (Push A1 s Γ) B1 (tsort s') (snext s')) (_ : der (Push A2 s Γ) B2 (tsort s') (snext s'))
                         (_ : der Γ t1 A1 s) (_ : der Γ t2 A2 s)
                         : der_eq Γ (snext s') (tsort s') (apply1 B1 t1) (apply1 B2 t2);
