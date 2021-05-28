
require ETT.XAst as ETT;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.HEq;

symbol τ_dΓ (Γ : TContext) : der_context (τ_Γ Γ);
rule τ_dΓ (TPush $Γ $s $A $dA _) ↪ der_context_push (τ_Γ $Γ) $s $A $dA (τ_dΓ $Γ)
with τ_dΓ TEmpty ↪ der_context_empty;

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
  @τ_T Γ (ShiftN id (tgetA id Γ)) (tgetS id Γ) (der_shift id (τ_dΓ Γ) (tgetD id Γ));

symbol tget (id : ETT.DBId) (Γ : TContext) : ε (τ_s (tgetS id Γ)) (tgetT id Γ);
rule tget db0 (TPush _ _ _ _ $a) ↪ $a
with tget (dbsucc $id) (TPush $t _ _ _ _) ↪ tget $id $t;
symbol tgetShift (id : ETT.DBId) (Γ : TContext) : ε (τ_s (tgetS id Γ)) (tgetTShift id Γ);
rule tgetShift db0 (TPush $Γ $s $A $dA $a)
     ↪ @τ_shift0T $Γ $s $s $A $A
          $dA $dA $a $a
with tgetShift (dbsucc $id) (TPush $Γ $s $A $dA $a)
  ↪ @τ_shift0T $Γ (tgetS $id $Γ) $s (ShiftN $id (tgetA $id $Γ)) $A
        (der_shift $id (τ_dΓ $Γ) (tgetD $id $Γ))
        $dA $a (tgetShift $id $Γ);

// Packed Context
constant symbol PCEmpty (Γ : TContext) : PContext Γ;
constant symbol PCPush
  {Γ : TContext} {s : ETT.Sort} {A1 A2 : ETT.Term} (P : PContext Γ)
  (dA1 : der (τ_Γ (projΓ1 P)) A1 (ETT.tsort s) (ETT.snext s))
  (dA2 : der (τ_Γ (projΓ2 P)) A2 (ETT.tsort s) (ETT.snext s))
  {a1 : ε (τ_s s) (τ_T (projΓ1 P) dA1)} {a2 : ε (τ_s s) (τ_T (projΓ2 P) dA2)}
  : H a1 a2 → PContext Γ;

// Necessary to keep confluence of pgetS
rule getS (τ_Γ (projΓ2 $P)) ↪ getS (τ_Γ (projΓ1 $P));

// Implementation of projΓ*
rule projΓ1 (PCEmpty $Γ) ↪ $Γ
with projΓ1 (@PCPush _ $s $A1 _ $P $dA1 _ $a1 _ _) ↪ TPush (projΓ1 $P) $s $A1 $dA1 $a1
with projΓ2 (PCEmpty $Γ) ↪ $Γ
with projΓ2 (@PCPush _ $s _ $A2 $P _ $dA2 _ $a2 _) ↪ TPush (projΓ2 $P) $s $A2 $dA2 $a2;

symbol pgetS {Γ : TContext} : ETT.DBId → PContext Γ → ETT.Sort;
rule pgetS $id $P ↪ tgetS $id (projΓ1 $P)
with pgetS $id $P ↪ tgetS $id (projΓ2 $P);
symbol pgetA1 {Γ : TContext} : ETT.DBId → PContext Γ → ETT.Term;
symbol pgetA2 {Γ : TContext} : ETT.DBId → PContext Γ → ETT.Term;
rule pgetA1 $id $P ↪ tgetA $id (projΓ1 $P)
with pgetA2 $id $P ↪ tgetA $id (projΓ2 $P);
symbol pgetΓ1 {Γ : TContext} : ETT.DBId → PContext Γ → TContext;
symbol pgetΓ2 {Γ : TContext} : ETT.DBId → PContext Γ → TContext;
rule pgetΓ1 $id $P ↪ tgetΓ $id (projΓ1 $P)
with pgetΓ2 $id $P ↪ tgetΓ $id (projΓ2 $P);

symbol pgetD1 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ)
              : der (τ_Γ (pgetΓ1 id HC)) (pgetA1 id HC) (ETT.tsort (pgetS id HC)) (ETT.snext (pgetS id HC));
symbol pgetD2 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ)
              : der (τ_Γ (pgetΓ2 id HC)) (pgetA2 id HC) (ETT.tsort (pgetS id HC)) (ETT.snext (pgetS id HC));
rule pgetD1 $id $P ↪ tgetD $id (projΓ1 $P)
with pgetD2 $id $P ↪ tgetD $id (projΓ2 $P);

symbol pget1 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : ε _ (τ (pgetΓ1 id HC) (pgetD1 id HC));
symbol pget2 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : ε _ (τ (pgetΓ2 id HC) (pgetD2 id HC));
rule pget1 $id $P ↪ tget $id (projΓ1 $P)
with pget2 $id $P ↪ tget $id (projΓ2 $P);

symbol pgetTShift1 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : U (τ_s (pgetS id HC));
symbol pgetTShift2 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : U (τ_s (pgetS id HC));
rule pgetTShift1 $id $P ↪ tgetTShift $id (projΓ1 $P)
with pgetTShift2 $id $P ↪ tgetTShift $id (projΓ2 $P);

symbol pgetShift1 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : ε _ (pgetTShift1 id HC);
symbol pgetShift2 {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : ε _ (pgetTShift2 id HC);
rule pgetShift1 $id $P ↪ tgetShift $id (projΓ1 $P)
with pgetShift2 $id $P ↪ tgetShift $id (projΓ2 $P);

symbol pgetH {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : H (pget1 id HC) (pget2 id HC);
rule pgetH db0 (PCPush _ _ _ $h) ↪ $h
with pgetH (dbsucc $id) (PCPush $P _ _ _) ↪ pgetH $id $P
with pgetH $id (PCEmpty $Γ) ↪ heq_refl _ (tget $id $Γ);

symbol pgetHShift {Γ : TContext} (id : ETT.DBId) (HC : PContext Γ) : H (pgetShift1 id HC) (pgetShift2 id HC);
rule pgetHShift db0 (@PCPush _ $s $A1 $A2 $P $dA1 $dA2 $a1 $a2 $h)
   ↪ heq_conj $h
        (@τ_shift0T_eq (projΓ1 $P) $s $s $A1 $A1 $dA1 $dA1 $a1)
        (@τ_shift0T_eq (projΓ2 $P) $s $s $A2 $A2 $dA2 $dA2 $a2)
with pgetHShift (dbsucc $id) (@PCPush _ $s $A1 $A2 $P $dA1 $dA2 $a1 $a2 _)
   ↪ heq_conj (pgetHShift $id $P)
        (@τ_shift0T_eq (projΓ1 $P) (pgetS $id $P) $s (ShiftN $id (pgetA1 $id $P)) $A1
            (der_shift $id (τ_dΓ (projΓ1 $P)) (pgetD1 $id $P))
            $dA1 $a1)
        (@τ_shift0T_eq (projΓ2 $P) (pgetS $id $P) $s (ShiftN $id (pgetA2 $id $P)) $A2
            (der_shift $id (τ_dΓ (projΓ2 $P)) (pgetD2 $id $P))
            $dA2 $a2)
with pgetHShift $id (PCEmpty $Γ) ↪ heq_refl _ (tgetShift $id $Γ);
