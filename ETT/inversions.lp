
require open ETT.main;
require ETT.itt as ITT;
symbol U : TYPE ≔ ITT.U ITT.s0;

// Properties that are true of a sub context
constant symbol WithSubΓ : Context → (Context → U) → TYPE;
constant symbol SubΓ {Γ : Context} {P : Context → U} (id : DBId) : ITT.ε ITT.s0 (P (getΓ Γ id)) → WithSubΓ Γ P;
symbol subId {Γ : Context} {P : Context → U} : WithSubΓ Γ P → DBId;
symbol subΓ {Γ : Context} {P : Context → U} (sub : WithSubΓ Γ P) : Context ≔ getΓ Γ (subId sub);
symbol subP {Γ : Context} {P : Context → U} (sub : WithSubΓ Γ P) : ITT.ε ITT.s0 (P (subΓ sub));
rule subId (SubΓ $id _) ↪ $id;
rule subP (SubΓ _ $P) ↪ $P;

// Lemmas
symbol substitution (Γ : Context) (s s' : Sort) (A B : Term) (C : Term) :
  der (Push A s Γ) C B s' → Π(u : Term), der Γ u A s → der Γ (apply1 C u) B s';
symbol inv_context : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(d : der Γ t T s), der_context Γ;
symbol inv_eq_context : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(d : der_eq Γ s T t1 t2), der_context Γ;
symbol inv_sort : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(d : der Γ t T s), WithSubΓ Γ (λ Γ, ider Γ T (tsort s) (snext s));
symbol inv_eq_sort : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(d : der_eq Γ s T t1 t2), WithSubΓ Γ (λ Γ, ider Γ T (tsort s) (snext s));
symbol inv_eq_t2 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t2 T s;
symbol inv_eq_t1 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t1 T s;

// Helpers
symbol der_subΓ (Γ : Context) (id : DBId) (dΓ : der_context Γ): der (getΓ Γ id) (get Γ id) (tsort (getS Γ id)) (snext (getS Γ id));
rule der_subΓ _ db0 (der_context_push _ _ _ $dA _) ↪ $dA
with der_subΓ _ (dbsucc $id) (der_context_push _ _ _ _ $dt) ↪ der_subΓ _ $id $dt;

// Definitions
rule inv_sort _ _ _ _ (der_var _ $id $dΓ) ↪ SubΓ $id (der_subΓ _ $id $dΓ);
