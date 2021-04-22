
require open ETT.main;
require ETT.itt as ITT;
symbol U : TYPE ≔ ITT.U ITT.s0;

// Lemmas
symbol substitution (Γ : Context) (s s' : Sort) (A B : Term) (C : Term) :
  der (Push A s Γ) C B s' → Π(u : Term), der Γ u A s → der Γ (apply1 C u) (apply1 B u) s';
symbol inv_context : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(d : der Γ t T s), der_context Γ;
symbol inv_eq_context : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(d : der_eq Γ s T t1 t2), der_context Γ;
symbol inv_sort : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(d : der Γ t T s), der Γ T (tsort s) (snext s);
symbol inv_eq_sort : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(d : der_eq Γ s T t1 t2), der Γ T (tsort s) (snext s);
symbol inv_eq_t2 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t2 T s;
symbol inv_eq_t1 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t1 T s;

symbol inv_type : Π(Γ : Context), Π(s s' : Sort), Π(A : Term), der Γ A (tsort s) s' → der Γ A (tsort s) (snext s);
symbol inv_eq_type : Π(Γ : Context), Π(s s' : Sort), Π(s1 s2 : Sort), der_eq Γ s' (tsort s) (tsort s1) (tsort s2) →
  der_eq Γ (snext (snext s1)) (tsort (snext s1)) (tsort s1) (tsort s1);

// Helpers
symbol der_subΓ (Γ : Context) (id : DBId) (dΓ : der_context Γ): der (getΓ Γ id) (get Γ id) (tsort (getS Γ id)) (snext (getS Γ id));
rule der_subΓ _ db0 (der_context_push _ _ _ $dA _) ↪ $dA
with der_subΓ _ (dbsucc $id) (der_context_push _ _ _ _ $dt) ↪ der_subΓ _ $id $dt;

symbol pushΓ {Γ : Context} {s : Sort} {T : Term} (d : der Γ T (tsort s) (snext s)) : der_context (Push T s Γ) ≔
  der_context_push Γ s T d (inv_context _ _ _ _ d);


// Definition of inv_sort
rule inv_sort _ _ _ _ (der_var $Γ $id $dΓ) ↪ der_shift $id $Γ _ _ _ (der_subΓ _ $id $dΓ)
with inv_sort _ _ _ _ (der_type_conv _ _ _ _ _ _ $deq) ↪ inv_eq_t2 _ _ _ _ _ $deq
with inv_sort _ _ _ _ (der_abs $Γ $s $s' $A _ $B $dA $dB _) ↪ der_prod $Γ $s $s' $A $B $dA $dB
with inv_sort _ _ _ _ (der_app $Γ $s $s' $A _ $u $B _ $dB _ $du) ↪ substitution $Γ $s (snext $s') $A (tsort $s') $B $dB $u $du
with inv_sort _ _ _ _ (der_pair $Γ $s $s' _ $A _ $B $dA _ $dB _) ↪ der_sigma $Γ $s $s' $A $B $dA $dB
with inv_sort _ _ _ _ (der_π1 _ _ _ _ _ _ $dA _ _) ↪ $dA
with inv_sort _ _ _ _ (der_π2 $Γ $s $s' $p $A $B $dA $dB $dp) ↪ substitution $Γ $s (snext $s') $A (tsort $s') $B $dB (π1 $A $B $p)
                                                                              (der_π1 $Γ $s $s' $p $A $B $dA $dB $dp)
with inv_sort _ _ _ _ (der_refl $Γ $s $u $A $dA $du) ↪ der_prop_type_eq $Γ $s $A $u $u $dA $du $du
with inv_sort _ _ _ _ (der_uip $Γ $s $e1 $e2 $u $v $A $de1 $de2) ↪ der_prop_type_eq $Γ $s (teq $A $u $v) $e1 $e2
                                                                                     (inv_sort _ _ _ _ $de1) $de1 $de2
with inv_sort _ _ _ _ (der_funext $Γ $s $s' $f $g $A _ $B $dA $dB $df $dg _)
  ↪ der_prop_type_eq $Γ (smax $s $s') (tfun $A $B) $f $g (der_prod $Γ $s $s' $A $B $dA $dB) $df $dg
;

// Definition of inv_eq*
rule inv_eq_sort _ _ _ _ _ (der_eq_refl _ _ _ _ $du) ↪ inv_sort _ _ _ _ $du
with inv_eq_t1   _ _ _ _ _ (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_t2   _ _ _ _ _ (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_sort _ _ _ _ _ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_sort _ _ _ _ _ $duv
with inv_eq_t1   _ _ _ _ _ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_t1   _ _ _ _ _ $duv
with inv_eq_t2   _ _ _ _ _ (der_eq_trans _ _ _ _ _ _ _ $dvw) ↪ inv_eq_t2   _ _ _ _ _ $dvw
with inv_eq_sort _ _ _ _ _ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_sort _ _ _ _ _ $duv
with inv_eq_t1   _ _ _ _ _ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t2   _ _ _ _ _ $duv
with inv_eq_t2   _ _ _ _ _ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t1  _ _ _ _ _ $duv
;
