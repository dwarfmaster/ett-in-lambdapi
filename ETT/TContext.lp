
require ETT.XAst as ETT;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.HEq;

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

// Context over
constant symbol COTail : Π(Γ : TContext), ContextOver Γ;
constant symbol COPush
  {Γ : TContext} (T : ContextOver Γ) {s : ETT.Sort} {A : ETT.Term}
  (dA : der (τ_Γ (Concat Γ T)) A (ETT.tsort s) (ETT.snext s))
  : ε (τ_s s) (τ_T (Concat Γ T) dA) → ContextOver Γ;

// Concat implementation
rule Concat $Γ (COTail _) ↪ $Γ
with Concat $Γ (COPush $T $dA $a) ↪ TPush (Concat $Γ $T) _ _ $dA $a;

// TContext
constant symbol PCEmpty (Γ : TContext) : PContext Γ (COTail Γ) (COTail Γ);
constant symbol PCPush
  {Γ : TContext} {T1 T2 : ContextOver Γ} {s : ETT.Sort} {A : ETT.Term}
  (_ : PContext Γ T1 T2)
  (dA1 : der (τ_Γ (Concat Γ T1)) A (ETT.tsort s) (ETT.snext s))
  (dA2 : der (τ_Γ (Concat Γ T2)) A (ETT.tsort s) (ETT.snext s))
  {a1 : ε (τ_s s) (τ_T (Concat Γ T1) dA1)} {a2 : ε (τ_s s) (τ_T (Concat Γ T2) dA2)}
  : H a1 a2 → PContext Γ (COPush T1 dA1 a1) (COPush T2 dA2 a2);

symbol PCSymm {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} : PContext Γ Γ1 Γ2 → PContext Γ Γ2 Γ1;
rule PCSymm (PCEmpty $Γ) ↪ PCEmpty $Γ
with PCSymm (PCPush $P $dA1 $dA2 $H) ↪ PCPush (PCSymm $P) $dA2 $dA1 (heq_symm $H);
