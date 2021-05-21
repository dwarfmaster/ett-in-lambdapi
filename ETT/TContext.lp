
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

// Packed Context
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

symbol pgetS {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} : ETT.DBId → PContext Γ Γ1 Γ2 → ETT.Sort;
rule pgetS db0 (@PCPush _ _ _ $s _ _ _ _ _ _ _) ↪ $s
with pgetS (dbsucc $id) (PCPush $P _ _ _) ↪ pgetS $id $P
with pgetS $id (PCEmpty $Γ) ↪ tgetS $id $Γ;
symbol pgetA {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} : ETT.DBId → PContext Γ Γ1 Γ2 → ETT.Term;
rule pgetA db0 (@PCPush _ _ _ _ $A _ _ _ _ _ _) ↪ $A
with pgetA (dbsucc $id) (PCPush $P _ _ _) ↪ pgetA $id $P
with pgetA $id (PCEmpty $Γ) ↪ tgetA $id $Γ;
symbol pgetΓ1 {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} : ETT.DBId → PContext Γ Γ1 Γ2 → TContext;
symbol pgetΓ2 {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} : ETT.DBId → PContext Γ Γ1 Γ2 → TContext;
rule pgetΓ1 db0 (@PCPush $Γ $T1 _ _ _ _ _ _ _ _ _) ↪ Concat $Γ $T1
with pgetΓ1 (dbsucc $id) (PCPush $P _ _ _) ↪ pgetΓ1 $id $P
with pgetΓ1 $id (PCEmpty $Γ) ↪ tgetΓ $id $Γ
with pgetΓ2 db0 (@PCPush $Γ _ $T2 _ _ _ _ _ _ _ _) ↪ Concat $Γ $T2
with pgetΓ2 (dbsucc $id) (PCPush $P _ _ _) ↪ pgetΓ2 $id $P
with pgetΓ2 $id (PCEmpty $Γ) ↪ tgetΓ $id $Γ;

symbol pgetD1 {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} (id : ETT.DBId) (HC : PContext Γ Γ1 Γ2)
              : der (τ_Γ (pgetΓ1 id HC)) (pgetA id HC) (ETT.tsort (pgetS id HC)) (ETT.snext (pgetS id HC));
symbol pgetD2 {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} (id : ETT.DBId) (HC : PContext Γ Γ1 Γ2)
              : der (τ_Γ (pgetΓ2 id HC)) (pgetA id HC) (ETT.tsort (pgetS id HC)) (ETT.snext (pgetS id HC));
rule pgetD1 db0 (PCPush _ $dA1 _ _) ↪ $dA1
with pgetD1 (dbsucc $id) (PCPush $P _ _ _) ↪ pgetD1 $id $P
with pgetD1 $id (PCEmpty $Γ) ↪ tgetD $id $Γ
with pgetD2 db0 (PCPush _ _ $dA2 _) ↪ $dA2
with pgetD2 (dbsucc $id) (PCPush $P _ _ _) ↪ pgetD2 $id $P
with pgetD2 $id (PCEmpty $Γ) ↪ tgetD $id $Γ;

symbol pget1 {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} (id : ETT.DBId) (HC : PContext Γ Γ1 Γ2)
             : ε _ (τ (pgetΓ1 id HC) (pgetD1 id HC));
symbol pget2 {Γ : TContext} {Γ1 Γ2 : ContextOver Γ} (id : ETT.DBId) (HC : PContext Γ Γ1 Γ2)
             : ε _ (τ (pgetΓ2 id HC) (pgetD2 id HC));
rule pget1 db0 (@PCPush _ _ _ _ _ _ _ _ $a1 _ _) ↪ $a1
with pget1 (dbsucc $id) (PCPush $P _ _ _) ↪ pget1 $id $P
with pget1 $id (PCEmpty $Γ) ↪ tget $id $Γ
with pget2 db0 (@PCPush _ _ _ _ _ _ _ _ _ $a2 _) ↪ $a2
with pget2 (dbsucc $id) (PCPush $P _ _ _) ↪ pget2 $id $P
with pget2 $id (PCEmpty $Γ) ↪ tget $id $Γ;
