
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.DeBruijn;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.Packing;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.Congruences;
require open ETT.TContext;
require open ETT.Translation;
require open ETT.EqualityTranslationLemmas;

// Computation
rule τ_eq $Γ (der_eq_beta _ $s $s' _ $A $t $B _ _ $dt $du)
  ↪ let IA : U (τ_s $s) ≔ τ_T $Γ (inv_sort (τ_dΓ $Γ) $du) in
     heq_symm (heq_trans
       (heq_symm (τ_subst_eq $Γ $dt $du))

       (heq_trans
         (eq_to_heq (@lift_eq (smax (τ_s $s) (τ_s $s')) (τ_s $s')
           (P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_I (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dt))
           (τ_I (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) (τ $Γ $du)) $dt)
           (λ(f : ε _ (P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_I (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dt))), f (τ $Γ $du))
           (λ(a : ε _ IA), τ (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dt)
           (τ_fun $Γ (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt)
             (der_prod (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt))
             (τ $Γ (der_abs (τ_Γ $Γ) $s $s' $A $t $B (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt) $dt)))
           (eq_of_transport
            (λ(a : ε _ IA), (τ (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dt))
            (τ_fun_eq $Γ (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt)
                      (der_prod (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt))))))

         (heq_of_transport
           (τ_fun $Γ (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt) (der_prod (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt))
                  (τ $Γ (der_abs (τ_Γ $Γ) $s $s' $A $t $B (inv_sort (τ_dΓ $Γ) $du) (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt) $dt))
                  (τ $Γ $du))
           (τ_substT_eq $Γ (inv_sort (pushIΓ (τ_dΓ $Γ) $du) $dt) $du))))

with τ_eq $Γ (der_eq_eta _ $s $s' $A $f $B $dA $dB $df)
  ↪ heq_symm (heq_trans
       (heq_of_transport (τ $Γ $df)
         (τ_fun_eq $Γ $dA $dB (inv_sort (τ_dΓ $Γ) $df)))
       (cong_lambda
         (λ a, τ_T (TPush $Γ $s $A $dA a) $dB)
         (λ a, τ_T (TPush $Γ $s $A $dA a)
                   (substitution (pushΓ $dA (τ_dΓ $Γ))
                                 (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)
                                 (der_var (Push $A $s (τ_Γ $Γ)) db0)))
         (τ_fun $Γ $dA $dB (inv_sort (τ_dΓ $Γ) $df) (τ $Γ $df))
         (τ $Γ (inv_eq_t1 (τ_dΓ $Γ) (der_eq_eta (τ_Γ $Γ) $s $s' $A $f $B $dA $dB $df)))
         (heq_refl (u (τ_s $s)) (τ_T $Γ $dA))
         (λ p, convertR $Γ (PCPush (PCEmpty $Γ) $dA $dA (projHEq p)) $dB
                 (substitution (pushΓ $dA (τ_dΓ $Γ))
                               (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)
                               (der_var (Push $A $s (τ_Γ $Γ)) db0)))

         (λ p, heq_trans
           (@cong_app _ _
             (τ_T $Γ $dA)
             (τ_T (TPush $Γ $s $A $dA (projT2 p)) (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_var (Push $A $s (τ_Γ $Γ)) db0)))
             (λ a, τ_T (TPush $Γ $s $A $dA a) $dB)
             (λ a, τ_T (TPush (TPush $Γ $s $A $dA (projT2 p)) $s (Shift $A)
                              (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_var (Push $A $s (τ_Γ $Γ)) db0)) a)
                       (der_shift1 $dA $dA (τ_dΓ $Γ) $dB))
             (τ_fun $Γ $dA $dB (inv_sort (τ_dΓ $Γ) $df) (τ $Γ $df))
             (τ_fun (TPush $Γ $s $A $dA (projT2 p))
                    (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_var (Push $A $s (τ_Γ $Γ)) db0))
                    (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)
                    (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_shift0 $dA (τ_dΓ $Γ) $df))
                    (τ (TPush $Γ $s $A $dA (projT2 p)) (der_shift0 $dA (τ_dΓ $Γ) $df)))
             (projT1 p)
             (τ (TPush $Γ $s $A $dA (projT2 p)) (der_var (Push $A $s (τ_Γ $Γ)) db0))
             (eq_to_heq (τ_shift0T_eq $Γ $dA $dA (projT2 p)))
             (λ p', heq_trans
               (eq_to_heq (τ_shift1T_eq $Γ $dB $dA $dA (projT1 p') (projT2 p)))
               (convertR (TPush $Γ $s $A $dA (projT2 p))
                         (PCPush (PCEmpty (TPush $Γ $s $A $dA (projT2 p)))
                                 (der_shift0 $dA (τ_dΓ $Γ) $dA)
                                 (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_var (Push $A $s (τ_Γ $Γ)) db0))
                                 (heq_extend_L (projT1 p') (projT2 p')
                                   (τ_shift0T_eq $Γ $dA $dA (projT2 p)) (projHEq p')))
                         (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)
                         (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)))
             (heq_conj
               (τ_shift0_eq $Γ (τ_dΓ $Γ) $df $dA (projT2 p))
               (τ_fun_eq $Γ $dA $dB (inv_sort (τ_dΓ $Γ) $df))
               (τ_fun_eq (TPush $Γ $s $A $dA (projT2 p))
                         (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_var (Push $A $s (τ_Γ $Γ)) db0))
                         (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)
                         (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_shift0 $dA (τ_dΓ $Γ) $df))))
             (heq_trans
               (projHEq p)
               (heq_trans
                 (heq_of_transport (projT2 p)
                   (τ_shift0T_eq $Γ $dA $dA (projT2 p)))
                 (heq_of_transport (τ_shift0T $Γ $dA $dA (projT2 p) (projT2 p))
                   (convert_T (TPush $Γ $s $A $dA (projT2 p))
                              (der_shift db0 (pushΓ $dA (τ_dΓ $Γ)) $dA)
                              (der_shift db0 (pushΓ $dA (τ_dΓ $Γ)) (der_getΓ db0 (pushΓ $dA (τ_dΓ $Γ)))))))))
           (heq_of_transport
             (τ_fun (TPush $Γ $s $A $dA (projT2 p))
                    (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_var (Push $A $s (τ_Γ $Γ)) db0))
                    (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)
                    (inv_sort (pushΓ $dA (τ_dΓ $Γ)) (der_shift0 $dA (τ_dΓ $Γ) $df))
                    (τ (TPush $Γ $s $A $dA (projT2 p)) (der_shift0 $dA (τ_dΓ $Γ) $df))
                    (τ (TPush $Γ $s $A $dA (projT2 p)) (der_var (Push $A $s (τ_Γ $Γ)) db0)))
             (τ_substT_eq (TPush $Γ $s $A $dA (projT2 p)) (der_shift1 $dA $dA (τ_dΓ $Γ) $dB)
               (der_var (Push $A $s (τ_Γ $Γ)) db0))))))

with τ_eq $Γ (der_eq_π1 _ $s $s' $u $A $v $B _ $du $dB $dv)
  ↪ eq_to_heq (inv_eq
      (@lift_eq (smax (τ_s $s) (τ_s $s')) (τ_s $s)
        (S (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dB))
        (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du))
        (λ(s : ε _ (S (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dB))), proj1 _ _ _ _ s)
        // u
        (mkS (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du))
            (λ(a : ε _ (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du))), τ_T (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dB)
            (τ $Γ $du)
            (τ_substT' $Γ $dB $du
              (transport (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dv) (substitution (τ_dΓ $Γ) $dB $du)) (τ $Γ $dv))))
        // v
        (τ_sum $Γ (inv_sort (τ_dΓ $Γ) $du) $dB (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) $dB)
          (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv)))
        // u = v
        (eq_of_transport
           (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv))
           (τ_sum_eq $Γ (inv_sort (τ_dΓ $Γ) $du) $dB (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) $dB)))))

with τ_eq $Γ (der_eq_π2 _ $s $s' $u $A $v $B _ $du $dB $dv)
  ↪ heq_symm
       (heq_trans
         // Equality from the translation of $v to the second projection of the untransported pair
         (heq_trans
           (heq_of_transport
             (τ $Γ $dv)
             (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dv) (substitution (τ_dΓ $Γ) $dB $du)))
           (heq_of_transport
             (transport (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dv) (substitution (τ_dΓ $Γ) $dB $du)) (τ $Γ $dv))
             (inv_eq (τ_substT_eq $Γ $dB $du))))

         (heq_trans
           // Equality between the projection of the pair and the transported pair
           (@lift_to_heq
             (smax (τ_s $s) (τ_s $s')) (τ_s $s')
             (S (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dB))
             (λ p, τ_T (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) (proj1 _ _ _ _ p)) $dB)
             (λ p, proj2 _ _ _ _ p)
             (mkS (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort (τ_dΓ $Γ) $du) a) $dB)
                  (τ $Γ $du)
                  (τ_substT' $Γ $dB $du (transport (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dv) (substitution (τ_dΓ $Γ) $dB $du)) (τ $Γ $dv))))
             (τ_sum $Γ (inv_sort (τ_dΓ $Γ) $du) $dB
                    (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) $dB)
                    (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv)))
             (heq_to_eq
               (heq_of_transport
                   (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv))
                   (τ_sum_eq $Γ (inv_sort (τ_dΓ $Γ) $du) $dB
                     (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) $dB)))))

           // Equality between the projection of the transported pair and the converted second element
           (heq_trans
             // Substitution
             (heq_of_transport
               (proj2 _ _ _ _ (τ_sum $Γ (inv_sort (τ_dΓ $Γ) $du) $dB
                                     (der_sigma (τ_Γ $Γ) $s $s' $A $B (inv_sort (τ_dΓ $Γ) $du) $dB)
                                     (τ $Γ (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv))))
               (τ_substT_eq $Γ $dB
                 (der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort (τ_dΓ $Γ) $du) $dB
                         (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv))))
             // Type conversion
             (heq_of_conversion $Γ
               (der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort (τ_dΓ $Γ) $du) $dB
                 (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv))
               (der_eq_cong_apply (τ_dΓ $Γ)
                 (der_eq_refl (τ_Γ $Γ) (ETT.snext $s) $A (ETT.tsort $s) (inv_sort (τ_dΓ $Γ) $du))
                 (der_eq_refl (Push $A $s (τ_Γ $Γ)) (ETT.snext $s') $B (ETT.tsort $s') $dB)
                 (der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv)
                 $dB $dB
                 (der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (inv_sort (τ_dΓ $Γ) $du) $dB
                   (der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (inv_sort (τ_dΓ $Γ) $du) $du $dB $dv)) $du)))))

with τ_eq $Γ (der_eq_conversion _ _ _ _ _ _ $deq $deqT)
  ↪ heq_conj
       (heq_conj
         (τ_eq $Γ $deq)
         (convert_T $Γ (inv_sort (τ_dΓ $Γ) (inv_eq_t1 (τ_dΓ $Γ) $deq)) (inv_eq_t1 (τ_dΓ $Γ) $deqT))
         (convert_T $Γ (inv_sort (τ_dΓ $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deq)) (inv_eq_t1 (τ_dΓ $Γ) $deqT)))
       (τ_eqT $Γ $deqT)
       (τ_eqT $Γ $deqT)

with τ_eq $Γ (der_eq_lift _ _ _ _ _ _ $de)
  ↪ let heq ≔ mkHeq (τ_T $Γ (inv_sort (τ_dΓ $Γ) (inv_teq_t1 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)))) (τ_T $Γ (inv_teq_sort (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)))
                     (τ $Γ (inv_teq_t1 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)))
                     (transport (convert_T $Γ (inv_sort (τ_dΓ $Γ) (inv_teq_t2 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de))) (inv_teq_sort (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)))
                                (τ $Γ (inv_teq_t2 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de))))
                     (convert_T $Γ (inv_sort (τ_dΓ $Γ) (inv_teq_t1 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de))) (inv_teq_sort (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)))
                     (τ_equality $Γ (inv_teq_sort (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)) (inv_teq_t1 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de))
                                    (inv_teq_t2 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)) (inv_sort (τ_dΓ $Γ) $de) (τ $Γ $de)) in
     heq_contract_R
       (τ $Γ (inv_teq_t1 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)))
       (τ $Γ (inv_teq_t2 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de)))
       (convert_T $Γ (inv_sort (τ_dΓ $Γ) (inv_teq_t2 (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de))) (inv_teq_sort (τ_dΓ $Γ) (inv_sort (τ_dΓ $Γ) $de))) heq

// Structural
with τ_eq $Γ (der_eq_refl _ _ _ _ $du)
  ↪ heq_refl (τ_T $Γ (inv_sort (τ_dΓ $Γ) $du)) (τ $Γ $du)
with τ_eq $Γ (der_eq_trans _ _ _ _ _ _ $duv $dvw)
  ↪ heq_trans
       (heq_trans
          (τ_eq $Γ $duv)
          (convert $Γ (inv_eq_t2 (τ_dΓ $Γ) $duv) (inv_eq_t1 (τ_dΓ $Γ) $dvw)))
       (τ_eq $Γ $dvw)
with τ_eq $Γ (der_eq_symm _ _ _ _ _ $duv)
  ↪ heq_symm (τ_eq $Γ $duv)
;
