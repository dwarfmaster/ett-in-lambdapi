
require ETT.XAst as ETT;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;

symbol tgetS (id : ETT.DBId) (Γ : TContext) : ETT.Sort ≔ getS (τ_Γ Γ) id;
symbol tgetA (id : ETT.DBId) (Γ : TContext) : ETT.Term ≔ get (τ_Γ Γ) id;

rule tgetΓ db0 (TPush $t _ _ _ _) ↪ $t
with tgetΓ (dbsucc $id) (TPush $t _ _ _ _) ↪ tgetΓ $id $t;
symbol tgetD (id : ETT.DBId) (Γ : TContext) : der (τ_Γ (tgetΓ id Γ)) (tgetA id Γ) (ETT.tsort (tgetS id Γ)) (ETT.snext (tgetS id Γ));
rule tgetD db0 (TPush _ _ _ $d _) ↪ $d
with tgetD (dbsucc $id) (TPush $t _ _ _ _) ↪ tgetD $id $t;

symbol tgetT (id : ETT.DBId) (Γ : TContext) : U (τ_s (tgetS id Γ)) ≔
  @τ_T (tgetΓ id Γ) (tgetA id Γ) (tgetS id Γ) (tgetD id Γ);
symbol tgetTShift (id : ETT.DBId) (Γ : TContext) : U (τ_s (tgetS id Γ)) ≔
  @τ_T Γ (ShiftN id (tgetA id Γ)) (tgetS id Γ) (der_shift id (τ_Γ Γ) _ _ _ (tgetD id Γ));

symbol tget (id : ETT.DBId) (Γ : TContext) : ε (τ_s (tgetS id Γ)) (tgetT id Γ);
rule tget db0 (TPush _ _ _ _ $a) ↪ $a
with tget (dbsucc $id) (TPush $t _ _ _ _) ↪ tget $id $t;
symbol tgetShift (id : ETT.DBId) (Γ : TContext) : ε (τ_s (tgetS id Γ)) (tgetTShift id Γ);
rule tgetShift db0 (TPush $Γ $s $A $dA $a)
     ↪ @τ_shift $Γ $s $s $A $A
          $dA $dA $a $a
with tgetShift (dbsucc $id) (TPush $Γ $s $A $dA $a)
  ↪ @τ_shift $Γ (tgetS $id $Γ) $s (ShiftN $id (tgetA $id $Γ)) $A
        (der_shift $id (τ_Γ $Γ) _ _ _ (tgetD $id $Γ))
        $dA $a (tgetShift $id $Γ);

// Converting in the context
// TODO this is false ! It is only true if a1 d1~d2 a2
symbol convert_Γ (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term) (d1 d2 : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                 (a1 : ε _ (τ_T Γ d1)) (a2 : ε _ (τ_T Γ d2))
                 (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) :
  ε _ (eq _ (u (τ_s s')) (τ_T (TPush Γ s A d1 a1) dB) (τ_T (TPush Γ s A d2 a2) dB));
