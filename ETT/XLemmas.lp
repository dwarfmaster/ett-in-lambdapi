
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;

// der_context accessors
symbol der_getΓ {Γ : Context} (id : DBId) (_ : der_context Γ) : der (getΓ Γ id) (get Γ id) (tsort (getS Γ id)) (snext (getS Γ id));
symbol der_subΓ {Γ : Context} (id : DBId) (_ : der_context Γ) : der_context (getΓ Γ id);
rule der_getΓ db0 (der_context_push _ _ _ $dA _) ↪ $dA
with der_getΓ (dbsucc $id) (der_context_push _ _ _ _ $dt) ↪ der_getΓ $id $dt
with der_subΓ db0 (der_context_push _ _ _ _ $dΓ) ↪ $dΓ
with der_subΓ (dbsucc $id) (der_context_push _ _ _ _ $dΓ) ↪ der_subΓ $id $dΓ
;

// Better der_context_push
symbol pushΓ {Γ : Context} {s : Sort} {T : Term} (d : der Γ T (tsort s) (snext s)) (dΓ : der_context Γ) : der_context (Push T s Γ) ≔
  der_context_push Γ s T d dΓ;

// Shifting derivation
symbol der_shift0 {Γ : Context} {t A T : Term} {s s' : Sort}
                  (_ : der Γ A (tsort s') (snext s')) (_ : der Γ t T s) :
  der (Push A s' Γ) (Shift t) (Shift T) s;
symbol der_eq_shift0 {Γ : Context} {t1 t2 A T : Term} {s s' : Sort}
                     (_ : der Γ A (tsort s') (snext s')) (_ : der_eq Γ s T t1 t2) :
  der_eq (Push A s' Γ) s (Shift T) (Shift t1) (Shift t2);
symbol der_shift1 {Γ : Context} {t A T B : Term} {s sa sb : Sort}
                  (_ : der Γ A (tsort sa) (snext sa))
                  (_ : der Γ B (tsort sb) (snext sb))
                  (_ : der (Push A sa Γ) t T s) : der (Push (Shift A) sa (Push B sb Γ)) (Shift1 t) (Shift1 T) s;

// Iterated shifting
symbol der_shift (id : DBId) {Γ : Context} (_ : der_context Γ) {t T : Term} {s : Sort} (_ : der (getΓ Γ id) t T s) : der Γ (ShiftN id t) (ShiftN id T) s;
rule der_shift db0 (der_context_push _ _ _ $dA _) $d ↪ der_shift0 $dA $d
with der_shift (dbsucc $id) (der_context_push _ _ _ $dA $dΓ) $d ↪ der_shift0 $dA (der_shift $id $dΓ $d);
symbol der_eq_shift (id : DBId) {Γ : Context} (_ : der_context Γ) {t1 t2 T : Term} {s : Sort} (_ : der_eq (getΓ Γ id) s T t1 t2)
                  : der_eq Γ s (ShiftN id T) (ShiftN id t1) (ShiftN id t2);

// Congruence for replacement
symbol der_eq_cong_apply (Γ : Context) {s s' : Sort} {A1 A2 B1 B2 t1 t2 : Term}
                         (_ : der_eq Γ (snext s) (tsort s) A1 A2) (_ : der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2)
                         (_ : der_eq Γ s A1 t1 t2)
                         (_ : der (Push A1 s Γ) B1 (tsort s') (snext s')) (_ : der (Push A2 s Γ) B2 (tsort s') (snext s'))
                         (_ : der Γ t1 A1 s) (_ : der Γ t2 A2 s)
                         : der_eq Γ (snext s') (tsort s') (apply1 B1 t1) (apply1 B2 t2);

symbol substitution {Γ : Context} {s s' : Sort} {A B C : Term} :
  der (Push A s Γ) C B s' → Π{u : Term}, der Γ u A s → der Γ (apply1 C u) (apply1 B u) s';
