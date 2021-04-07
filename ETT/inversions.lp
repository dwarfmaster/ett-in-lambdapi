
require open ETT.main;
require ETT.itt as ITT;

// Lemmas
symbol substitution (Γ : Context) (s s' : Sort) (A B : Term) (C : Term) :
  der (Push A s Γ) C B s' → Π(u : Term), der Γ u A s → der Γ (apply1 C u) B s';
symbol inv_context : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(d : der Γ t T s), der_context Γ;
symbol inv_eq_context : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(d : der_eq Γ s T t1 t2), der_context Γ;
symbol inv_sort : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(d : der Γ t T s), der Γ T (tsort s) (snext s);
symbol inv_eq_sort : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(d : der_eq Γ s T t1 t2), der Γ T (tsort s) (snext s);
symbol inv_eq_t2 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t2 T s;
symbol inv_eq_t1 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t1 T s;

// Definitions
// rule inv_eq_t1 ↪
//   der_eq_ind ITT.s0 (λ _ _ _, ITT.⊤ ITT.s0)
//              (λ T t1 _ _, ITT.ider t1 T)
//     // Types
//     (λ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     // Structural rules
//     (λ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     // λ-calculus terms
//     (λ _ _ _ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     (λ _ _ _ _ _ _ _ _ _ _ _, ITT.I ITT.s0)
//     // Computation
//     (λ s s' u A t B dA dB dt du _ _ _ _, der_app s s' A (tabs A B t) u B dA dB (der_abs s s' A t B dA dB dt) du)
//     (λ s s' u A w E dA du dE dw _ _ _ _, der_J s s' A u u (trefl A u) w E dA du du dE (der_refl s u A dA du) dw)
//     (λ s s' u A v B dA du dB dv _ _ _ _, der_π1 (tpair A B u v) A B (der_pair s s' u A v B dA du dB dv))
//     (λ s s' u A v B dA du dB dv _ _ _ _, der_type_conv (π2 A B (tpair A B u v)) (B (π1 A B (tpair A B u v))) (B u) s'
//                                                        (der_π2 (tpair A B u v) A B (der_pair s s' u A v B dA du dB dv))
//                                                        (der_eq_context (snext s') (π1 A B (tpair A B u v)) u A (tsort s') B B
//                                                                        (der_eq_π1 s s' u A v B dA du dB dv) (der_sort s')
//                                                                        (λ v, der_eq_refl (B (VAR v A)) (tsort s') (dB v))))
//     (λ s t1 t2 T1 T2 dT1 dT2 deqt deqT _ _ Heqt _, der_type_conv t1 T1 T2 s Heqt deqT)
//     (λ e u v A de _, inv_teq_t1 u v A e de)
//     // Congruence
//     (λ u A dA _, dA)
//     (λ u v w A du dv Hu Hv, Hu)
//     (λ u v A d H, inv_eq_t2 A u v d)
//     (λ s u u' A B C C' du dB dC Hu HB HC, substitution A B C (λ v, HC v) u Hu);
