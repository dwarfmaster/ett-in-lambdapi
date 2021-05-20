
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.Congruences;
require open ETT.TContext;
require open ETT.Translation;

// Cheater helper
symbol magic {s : Sort} (A : U s) : ε s A;

// Computation
rule τ_eq $Γ (der_eq_beta _ $s $s' _ $A $t $B _ _ $dt $du)
  ↪ let IA : U (τ_s $s) ≔ τ_T $Γ (inv_sort $du) in
     heq_symm (heq_trans
       (heq_symm (τ_subst_eq $Γ $dt $du))

       (heq_trans
         (eq_to_heq (@lift_eq (smax (τ_s $s) (τ_s $s')) (τ_s $s')
           (P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_T (TPush $Γ $s $A (inv_sort $du) a) (inv_sort $dt)))
           (τ_T (TPush $Γ $s $A (inv_sort $du) (τ $Γ $du)) (inv_sort $dt))
           (λ(f : ε _ (P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_T (TPush $Γ $s $A (inv_sort $du) a) (inv_sort $dt)))), f (τ $Γ $du))
           (λ(a : ε _ IA), τ (TPush $Γ $s $A (inv_sort $du) a) $dt)
           (τ_fun $Γ (inv_sort $du) (inv_sort $dt) (der_prod (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) (inv_sort $dt))
             (τ $Γ (der_abs (τ_Γ $Γ) $s $s' $A $t $B (inv_sort $du) (inv_sort $dt) $dt)))
           (eq_of_transport
            (λ(a : ε _ IA), (τ (TPush $Γ $s $A (inv_sort $du) a) $dt))
            (τ_fun_eq $Γ (inv_sort $du) (inv_sort $dt) (der_prod (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) (inv_sort $dt))))))

         (heq_of_transport
           (τ_fun $Γ (inv_sort $du) (inv_sort $dt) (der_prod (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) (inv_sort $dt))
                  (τ $Γ (der_abs (τ_Γ $Γ) $s $s' $A $t $B (inv_sort $du) (inv_sort $dt) $dt))
                  (τ $Γ $du))
           (τ_substT_eq $Γ (inv_sort $dt) $du))))

with τ_eq $Γ (der_eq_π1 _ $s $s' $u $A $v $B _ $du $dB $dv)
  ↪ eq_to_heq (inv_eq
      (@lift_eq (smax (τ_s $s) (τ_s $s')) (τ_s $s)
        (S (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort $du) a) $dB))
        (τ_T $Γ (inv_sort $du))
        (λ(s : ε _ (S (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort $du) a) $dB))), proj1 _ _ _ _ s)
        // u
        (mkS (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort $du))
            (λ(a : ε _ (τ_T $Γ (inv_sort $du))), τ_T (TPush $Γ $s $A (inv_sort $du) a) $dB)
            (τ $Γ $du)
            (τ_substT' $Γ $dB $du
              (transport (convert_T $Γ (inv_sort $dv) (substitution $dB $du)) (τ $Γ $dv))))
        // v
        (τ_sum $Γ (inv_sort $du) $dB (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) $dB)
          (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv)))
        // u = v
        (eq_of_transport
           (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv))
           (τ_sum_eq $Γ (inv_sort $du) $dB (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) $dB)))))

with τ_eq $Γ (der_eq_π2 _ $s $s' $u $A $v $B _ $du $dB $dv)
  ↪ heq_symm
       (heq_trans
         // Equality from the translation of $v to the second projection of the untransported pair
         (heq_trans
           (heq_of_transport
             (τ $Γ $dv)
             (convert_T $Γ (inv_sort $dv) (substitution $dB $du)))
           (heq_of_transport
             (transport (convert_T $Γ (inv_sort $dv) (substitution $dB $du)) (τ $Γ $dv))
             (inv_eq (τ_substT_eq $Γ $dB $du))))

         (heq_trans
           // Equality between the projection of the pair and the transported pair
           (@lift_to_heq
             (smax (τ_s $s) (τ_s $s')) (τ_s $s')
             (S (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort $du) a) $dB))
             (λ p, τ_T (TPush $Γ $s $A (inv_sort $du) (proj1 _ _ _ _ p)) $dB)
             (λ p, proj2 _ _ _ _ p)
             (mkS (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort $du) a) $dB)
                  (τ $Γ $du)
                  (τ_substT' $Γ $dB $du (transport (convert_T $Γ (inv_sort $dv) (substitution $dB $du)) (τ $Γ $dv))))
             (τ_sum $Γ (inv_sort $du) $dB
                    (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) $dB)
                    (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv)))
             (heq_to_eq
               (heq_of_transport
                   (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv))
                   (τ_sum_eq $Γ (inv_sort $du) $dB
                     (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) $dB)))))

           // Equality between the projection of the transported pair and the converted second element
           (heq_trans
             // Substitution
             (heq_of_transport
               (proj2 _ _ _ _ (τ_sum $Γ (inv_sort $du) $dB
                                     (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort $du) $dB)
                                     (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv))))
               (τ_substT_eq $Γ $dB
                 (der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort $du) $dB
                         (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv))))
             // Type conversion
             (heq_trans
               (heq_of_transport
                 (τ $Γ (der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort $du) $dB
                          (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv)))
                 (convert_T $Γ
                   (substitution $dB (der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort $du) $dB
                                       (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv)))
                   (inv_eq_t1 (der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                 (der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv) $dB))))
               (heq_of_transport
                 (transport
                   (convert_T $Γ
                     (substitution $dB (der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort $du) $dB
                                         (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv)))
                     (inv_eq_t1 (der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                   (der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv) $dB)))
                   (τ $Γ (der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort $du) $dB
                                 (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv))))
                 (τ_eqT $Γ
                        (der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                (der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv) $dB)))))))

// TODO Conversion
// rule τ_eq $Γ _ _ _ _ (ETT.der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deq $deqT)
//   ↪ mkHeq
//        (τ_T $Γ _ _ (I.inv_eq_t2 _ _ _ _ _ $deqT))
//        (τ_T $Γ _ _ (I.inv_eq_t2 _ _ _ _ _ $deqT))
//        (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq) $deqT))
//        (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq) $deqT))
//        (ITT.trans_eq (ITT.trans_eq (ITT.inv_eq (τ_eqT $Γ _ _ _ $deqT)) (ITT.inv_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT))))
//                      (ITT.trans_eq (getTeq _ _ _ _ (τ_eq $Γ _ _ _ _ $deq))
//                                    (ITT.trans_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT)) (τ_eqT $Γ _ _ _ $deqT))))
//        (magic _
//          (ITT.eq _ (τ_T $Γ _ _ (I.inv_eq_t2 _ _ _ _ _ $deqT))
//            (transport _ _ _ (ITT.trans_eq (ITT.trans_eq (ITT.inv_eq (τ_eqT $Γ _ _ _ $deqT)) (ITT.inv_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT))))
//                                           (ITT.trans_eq (getTeq _ _ _ _ (τ_eq $Γ _ _ _ _ $deq))
//                                                         (ITT.trans_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT)) (τ_eqT $Γ _ _ _ $deqT))))
//               (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq) $deqT)))
//            (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq) $deqT))))

with τ_eq $Γ (der_eq_lift _ _ _ _ _ _ $de)
  ↪ let heq ≔ mkHeq (τ_T $Γ (inv_sort (inv_teq_t1 $de))) (τ_T $Γ (inv_teq_sort $de))
                     (τ $Γ (inv_teq_t1 $de))
                     (transport (convert_T $Γ (inv_sort (inv_teq_t2 $de)) (inv_teq_sort $de)) (τ $Γ (inv_teq_t2 $de)))
                     (convert_T $Γ (inv_sort (inv_teq_t1 $de)) (inv_teq_sort $de))
                     (τ_equality $Γ $de (τ $Γ $de)) in
     heq_extend_R
       (τ $Γ (inv_teq_t1 $de))
       (τ $Γ (inv_teq_t2 $de))
       (convert_T $Γ (inv_sort (inv_teq_t2 $de)) (inv_teq_sort $de)) heq

// Congruence
with τ_eq $Γ (der_eq_refl _ _ _ _ $du)
  ↪ heq_refl (τ_T $Γ (inv_sort $du)) (τ $Γ $du)
with τ_eq $Γ (der_eq_trans _ _ _ _ _ _ $duv $dvw)
  ↪ heq_trans
       (heq_trans
          (τ_eq $Γ $duv)
          (convert $Γ (inv_eq_t2 $duv) (inv_eq_t1 $dvw)))
       (τ_eq $Γ $dvw)
with τ_eq $Γ (der_eq_symm _ _ _ _ _ $duv)
  ↪ heq_symm (τ_eq $Γ $duv)

// Context
// prod
with τ_eq $Γ (der_eq_ctx_prod_domain _ $s $s' $A $A' $B $deqA $dB)
  ↪ eq_to_heq (eq_prod
            (λ a, τ_T (TPush $Γ $s $A  (inv_eq_t1 $deqA) a) $dB)
            (λ a, τ_T (TPush $Γ $s $A' (inv_eq_t2 $deqA) a) (der_conv_in_ctx (τ_Γ $Γ) $s (ETT.snext $s') $A $A' $B (ETT.tsort $s') $deqA $dB))
            (τ_eqT $Γ $deqA)
            (λ a, τ_convT_in_ctx $Γ $deqA $dB a))
with τ_eq $Γ (der_eq_ctx_prod_codomain _ $s _ $A _ _ $dA $deqB)
  ↪ eq_to_heq (eq_prod
            (λ a, τ_T (TPush $Γ $s $A $dA a) (inv_eq_t1 $deqB))
            (λ a, τ_T (TPush $Γ $s $A $dA a) (inv_eq_t2 $deqB))
            (refl (snext (τ_s $s)) (u (τ_s $s)) (τ_T $Γ $dA))
            (λ a, τ_eqT (TPush $Γ $s $A $dA a) $deqB))
// tabs
with τ_eq $Γ (der_eq_ctx_tabs_domain _ $s $s' $A $A' $B $t $deqA $dB $dt)
  ↪ magic (τ_eq_type $Γ (der_eq_ctx_tabs_domain (τ_Γ $Γ) $s $s' $A $A' $B $t $deqA $dB $dt))
// with τ_eq $Γ (der_eq_ctx_tabs_codomain _ $s $s' $A $B $B' _ $dA $deqB $dt)
//   ↪ heq_trans
//        (heq_funext (τ_T $Γ $dA)
//          (λ a, τ_T (TPush $Γ $s $A $dA a) (inv_eq_t1 $deqB))
//          (λ a, τ_T (TPush $Γ $s $A $dA a) (inv_eq_t2 $deqB))
//          (λ(a : ε _ (τ_T $Γ $dA)), transport (convert_T (TPush $Γ $s $A $dA a) (inv_sort $dt) (inv_eq_t1 $deqB)) (τ (TPush $Γ $s $A $dA a) $dt))
//          (λ(a : ε _ (τ_T $Γ $dA)), transport (convert_T (TPush $Γ $s $A $dA a) (inv_eq_t2 $deqB) (inv_eq_t2 $deqB))
//                                    (transport (τ_eqT (TPush $Γ $s $A $dA a) $deqB)
//                                    (transport (convert_T (TPush $Γ $s $A $dA a) (inv_sort $dt) (inv_eq_t1 $deqB))
//                                    (τ (TPush $Γ $s $A $dA a) $dt))))
//          (λ a, heq_trans
//            (heq_of_transport
//              (transport (convert_T (TPush $Γ $s $A $dA a) (inv_sort $dt) (inv_eq_t1 $deqB)) (τ (TPush $Γ $s $A $dA a) $dt))
//              (τ_eqT (TPush $Γ $s $A $dA a) $deqB))
//            (heq_of_transport
//              (transport (τ_eqT (TPush $Γ $s $A $dA a) $deqB)
//                         (transport (convert_T (TPush $Γ $s $A $dA a) (inv_sort $dt) (inv_eq_t1 $deqB))
//                                    (τ (TPush $Γ $s $A $dA a) $dt)))
//              (convert_T (TPush $Γ $s $A $dA a) (inv_eq_t2 $deqB) (inv_eq_t2 $deqB)))))
//        (heq_trans
//          (heq_of_transport
//            (λ(a : ε _ (τ_T $Γ $dA)), transport (convert_T (TPush $Γ $s $A $dA a) (inv_eq_t2 $deqB) (inv_eq_t2 $deqB))
//                                      (transport (τ_eqT (TPush $Γ $s $A $dA a) $deqB)
//                                      (transport (convert_T (TPush $Γ $s $A $dA a) (inv_sort $dt) (inv_eq_t1 $deqB))
//                                      (τ (TPush $Γ $s $A $dA a) $dt))))
//            (convert_T $Γ (der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (inv_eq_t2 $deqB)) (der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (inv_eq_t2 $deqB))))
//          (heq_of_transport
//            (transport (convert_T $Γ (der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (inv_eq_t2 $deqB)) (der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (inv_eq_t2 $deqB)))
//              (λ(a : ε _ (τ_T $Γ $dA)), transport (convert_T (TPush $Γ $s $A $dA a) (inv_eq_t2 $deqB) (inv_eq_t2 $deqB))
//                                        (transport (τ_eqT (TPush $Γ $s $A $dA a) $deqB)
//                                        (transport (convert_T (TPush $Γ $s $A $dA a) (inv_sort $dt) (inv_eq_t1 $deqB))
//                                        (τ (TPush $Γ $s $A $dA a) $dt)))))
//            (τ_eqT $Γ (der_eq_symm (τ_Γ $Γ) (ETT.snext (ETT.smax $s $s')) (ETT.tfun $A $B) (ETT.tfun $A $B') (ETT.tsort (ETT.smax $s $s'))
//                        (der_eq_ctx_prod_codomain (τ_Γ $Γ) $s $s' $A $B $B' $dA $deqB)))))
;
