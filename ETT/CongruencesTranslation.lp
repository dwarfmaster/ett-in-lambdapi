
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

// Lambda calculus
rule τ_eq $Γ (der_eq_cong_tfun _ $s _ $A1 $A2 _ _ $deqA $deqB $dB1 $dB2)
  ↪ cong_prod
       (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) a) $dB1)
       (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) a) $dB2)
       (τ_eq $Γ $deqA)
       (λ p, heq_trans
         (convert (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $dB1 (inv_eq_t1 (push1Γ (τ_dΓ $Γ) $deqA) $deqB))
         (heq_trans
           (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $deqB)
           (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 (τ_dΓ $Γ) $deqA) (inv_eq_t2 (τ_dΓ $Γ) $deqA) (projHEq p)) (inv_eq_t2 (push1Γ (τ_dΓ $Γ) $deqA) $deqB) $dB2)))
with τ_eq $Γ (der_eq_cong_tabs _ $s $s' $A1 $A2 $B1 $B2 _ $t2 $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ heq_trans
       (cong_lambda
         (λ a, τ_T (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) a) (inv_sort (push1Γ (τ_dΓ $Γ) $deqA) $dt1))
         (λ a, τ_T (TPush $Γ $s $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) a) (inv_sort (push2Γ (τ_dΓ $Γ) $deqA) $dt2))
         (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) a) $dt1)
         (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) a) $dt2)
         (τ_eq $Γ $deqA)
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) (inv_sort (push1Γ (τ_dΓ $Γ) $deqA) $dt1) (inv_eq_t1 (push1Γ (τ_dΓ $Γ) $deqA) $deqB))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $deqB)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 (τ_dΓ $Γ) $deqA) (inv_eq_t2 (τ_dΓ $Γ) $deqA) (projHEq p))
                          (inv_eq_t2 (push1Γ (τ_dΓ $Γ) $deqA) $deqB) (inv_sort (push2Γ (τ_dΓ $Γ) $deqA) $dt2))))
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $dt1 (inv_eq_t1 (push1Γ (τ_dΓ $Γ) $deqA) $deqt))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $deqt)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 (τ_dΓ $Γ) $deqA) (inv_eq_t2 (τ_dΓ $Γ) $deqA) (projHEq p)) (inv_eq_t2 (push1Γ (τ_dΓ $Γ) $deqA) $deqt) $dt2))))
       (heq_of_conversion $Γ
         (der_abs (τ_Γ $Γ) $s $s' $A2 $t2 $B2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 $dt2)
         (der_eq_symm _ _ _ _ _ (der_eq_cong_tfun (τ_Γ $Γ) $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)))
with τ_eq $Γ (der_eq_cong_tapp _ $s $s' $A1 $A2 _ $B2 _ $f2 _ $a2 $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
  ↪ heq_trans
       (heq_conj
         (cong_app
           (λ a, τ (TPush $Γ $s $A1 (inv_sort (τ_dΓ $Γ) $da1) a) $dB1)
           (λ a, τ (TPush $Γ $s $A2 (inv_sort (τ_dΓ $Γ) $da2) a) $dB2)
           (heq_trans
             (convert $Γ (inv_sort (τ_dΓ $Γ) $da1) (inv_eq_t1 (τ_dΓ $Γ) $deqA))
             (heq_trans
               (τ_eq $Γ $deqA)
               (convert $Γ (inv_eq_t2 (τ_dΓ $Γ) $deqA) (inv_sort (τ_dΓ $Γ) $da2))))
           (λ p, heq_trans
             (convert (TPush $Γ $s $A1 (inv_sort (τ_dΓ $Γ) $da1) (projT1 p)) $dB1 (inv_eq_t1 (pushIΓ (τ_dΓ $Γ) $da1) $deqB))
             (heq_trans
               (τ_eq (TPush $Γ $s $A1 (inv_sort (τ_dΓ $Γ) $da1) (projT1 p)) $deqB)
               (convertR $Γ (PCPush (PCEmpty $Γ) (inv_sort (τ_dΓ $Γ) $da1) (inv_sort (τ_dΓ $Γ) $da2) (projHEq p)) (inv_eq_t2 (pushIΓ (τ_dΓ $Γ) $da1) $deqB) $dB2)))
           (heq_conj
             (heq_trans
               (convert $Γ $df1 (inv_eq_t1 (τ_dΓ $Γ) $deqf))
               (heq_trans
                 (τ_eq $Γ $deqf)
                 (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqf) $df2)))
             (τ_fun_eq $Γ (inv_sort (τ_dΓ $Γ) $da1) $dB1 (inv_sort (τ_dΓ $Γ) $df1))
             (τ_fun_eq $Γ (inv_sort (τ_dΓ $Γ) $da2) $dB2 (inv_sort (τ_dΓ $Γ) $df2)))
           (heq_trans
             (convert $Γ $da1 (inv_eq_t1 (τ_dΓ $Γ) $deqa))
             (heq_trans
               (τ_eq $Γ $deqa)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqa) $da2))))
         (τ_substT_eq $Γ $dB1 $da1)
         (τ_substT_eq $Γ $dB2 $da2))
       (heq_of_conversion $Γ
         (der_app (τ_Γ $Γ) $s $s' $A2 $f2 $a2 $B2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 $df2 $da2)
         (der_eq_symm _ _ _ _ _ (der_eq_cong_apply (τ_dΓ $Γ) $deqA $deqB $deqa $dB1 $dB2 $da1 $da2)))

// Pairs
with τ_eq $Γ (der_eq_cong_tsum _ $s _ $A1 $A2 _ _ $deqA $deqB $dB1 $dB2)
  ↪ cong_sum
       (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) a) $dB1)
       (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) a) $dB2)
       (τ_eq $Γ $deqA)
       (λ p, heq_trans
         (convert (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $dB1 (inv_eq_t1 (push1Γ (τ_dΓ $Γ) $deqA) $deqB))
         (heq_trans
           (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $deqB)
           (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 (τ_dΓ $Γ) $deqA) (inv_eq_t2 (τ_dΓ $Γ) $deqA) (projHEq p)) (inv_eq_t2 (push1Γ (τ_dΓ $Γ) $deqA) $deqB) $dB2)))
with τ_eq $Γ (der_eq_cong_tpair _ $s $s' $A1 $A2 $B1 $B2 _ $a2 _ $b2 $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
  ↪ heq_trans
         (cong_pair
           (λ a, τ (TPush $Γ $s $A1 (inv_sort (τ_dΓ $Γ) $da1) a) $dB1)
           (λ a, τ (TPush $Γ $s $A2 (inv_sort (τ_dΓ $Γ) $da2) a) $dB2)
           (heq_trans
             (convert $Γ (inv_sort (τ_dΓ $Γ) $da1) (inv_eq_t1 (τ_dΓ $Γ) $deqA))
             (heq_trans
               (τ_eq $Γ $deqA)
               (convert $Γ (inv_eq_t2 (τ_dΓ $Γ) $deqA) (inv_sort (τ_dΓ $Γ) $da2))))
           (λ p, heq_trans
             (convert (TPush $Γ $s $A1 (inv_sort (τ_dΓ $Γ) $da1) (projT1 p)) $dB1 (inv_eq_t1 (pushIΓ (τ_dΓ $Γ) $da1) $deqB))
             (heq_trans
               (τ_eq (TPush $Γ $s $A1 (inv_sort (τ_dΓ $Γ) $da1) (projT1 p)) $deqB)
               (convertR $Γ (PCPush (PCEmpty $Γ) (inv_sort (τ_dΓ $Γ) $da1) (inv_sort (τ_dΓ $Γ) $da2) (projHEq p)) (inv_eq_t2 (pushIΓ (τ_dΓ $Γ) $da1) $deqB) $dB2)))
           (heq_trans
             (convert $Γ $da1 (inv_eq_t1 (τ_dΓ $Γ) $deqa))
             (heq_trans
               (τ_eq $Γ $deqa)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqa) $da2)))
           (heq_conj
             (heq_conj
               (heq_trans
                 (convert $Γ $db1 (inv_eq_t1 (τ_dΓ $Γ) $deqb))
                 (heq_trans
                   (τ_eq $Γ $deqb)
                   (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqb) $db2)))
               (convert_T $Γ (inv_sort (τ_dΓ $Γ) $db1) (substitution (τ_dΓ $Γ) $dB1 $da1))
               (convert_T $Γ (inv_sort (τ_dΓ $Γ) $db2) (substitution (τ_dΓ $Γ) $dB2 $da2)))
             (inv_eq (τ_substT_eq $Γ $dB1 $da1))
             (inv_eq (τ_substT_eq $Γ $dB2 $da2))))
         (heq_of_conversion $Γ
           (der_pair (τ_Γ $Γ) $s $s' $a2 $A2 $b2 $B2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2 $dB2 $db2)
           (der_eq_symm _ _ _ _ _ (der_eq_cong_tsum (τ_Γ $Γ) $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)))
with τ_eq $Γ (der_eq_cong_π1 _ $s $s' $A1 $A2 _ $B2 _ $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ heq_trans
       (cong_proj1
         (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) a) $dB1)
         (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) a) $dB2)
         (τ_eq $Γ $deqA)
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $dB1 (inv_eq_t1 (push1Γ (τ_dΓ $Γ) $deqA) $deqB))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $deqB)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 (τ_dΓ $Γ) $deqA) (inv_eq_t2 (τ_dΓ $Γ) $deqA) (projHEq p)) (inv_eq_t2 (push1Γ (τ_dΓ $Γ) $deqA) $deqB) $dB2)))
         (heq_conj
           (heq_trans
             (convert $Γ $dp1 (inv_eq_t1 (τ_dΓ $Γ) $deqp))
             (heq_trans
               (τ_eq $Γ $deqp)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqp) $dp2)))
           (τ_sum_eq $Γ (inv_eq_t1 (τ_dΓ $Γ) $deqA) $dB1 (inv_sort (τ_dΓ $Γ) $dp1))
           (τ_sum_eq $Γ (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 (inv_sort (τ_dΓ $Γ) $dp2))))
       (heq_of_conversion $Γ
         (der_π1 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 $dp2)
         (der_eq_symm _ _ _ _ _ $deqA))
with τ_eq $Γ (der_eq_cong_π2 _ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ heq_trans
       (heq_conj
         (cong_proj2
           (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) a) $dB1)
           (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) a) $dB2)
           (τ_eq $Γ $deqA)
           (λ p, heq_trans
             (convert (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $dB1 (inv_eq_t1 (push1Γ (τ_dΓ $Γ) $deqA) $deqB))
             (heq_trans
               (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) (projT1 p)) $deqB)
               (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 (τ_dΓ $Γ) $deqA) (inv_eq_t2 (τ_dΓ $Γ) $deqA) (projHEq p)) (inv_eq_t2 (push1Γ (τ_dΓ $Γ) $deqA) $deqB) $dB2)))
           (heq_conj
             (heq_trans
               (convert $Γ $dp1 (inv_eq_t1 (τ_dΓ $Γ) $deqp))
               (heq_trans
                 (τ_eq $Γ $deqp)
                 (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqp) $dp2)))
             (τ_sum_eq $Γ (inv_eq_t1 (τ_dΓ $Γ) $deqA) $dB1 (inv_sort (τ_dΓ $Γ) $dp1))
             (τ_sum_eq $Γ (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 (inv_sort (τ_dΓ $Γ) $dp2))))
         (τ_substT_eq $Γ $dB1 (der_π1 (τ_Γ $Γ) $s $s' $p1 $A1 $B1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) $dB1 $dp1))
         (τ_substT_eq $Γ $dB2 (der_π1 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 $dp2)))
       (heq_of_conversion $Γ
         (der_π2 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 $dp2)
         (der_eq_symm _ _ _ _ _
          (der_eq_cong_apply (τ_dΓ $Γ) $deqA $deqB
           (der_eq_cong_π1 (τ_Γ $Γ) $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
           $dB1 $dB2
           (der_π1 (τ_Γ $Γ) $s $s' $p1 $A1 $B1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) $dB1 $dp1)
           (der_π1 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $dB2 $dp2))))

// Equalities
with τ_eq $Γ (der_eq_cong_teq _ _ _ _ _ _ _ _ $deqA $deqa $deqb $da1 $da2 $db1 $db2)
  ↪ cong_eq
       (τ_eq $Γ $deqA)
       (heq_conj
         (heq_trans
           (convert $Γ $da1 (inv_eq_t1 (τ_dΓ $Γ) $deqa))
           (heq_trans
             (τ_eq $Γ $deqa)
             (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqa) $da2)))
         (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da1) (inv_eq_t1 (τ_dΓ $Γ) $deqA))
         (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da2) (inv_eq_t2 (τ_dΓ $Γ) $deqA)))
       (heq_conj
         (heq_trans
           (convert $Γ $db1 (inv_eq_t1 (τ_dΓ $Γ) $deqb))
           (heq_trans
             (τ_eq $Γ $deqb)
             (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqb) $db2)))
         (convert_T $Γ (inv_sort (τ_dΓ $Γ) $db1) (inv_eq_t1 (τ_dΓ $Γ) $deqA))
         (convert_T $Γ (inv_sort (τ_dΓ $Γ) $db2) (inv_eq_t2 (τ_dΓ $Γ) $deqA)))
with τ_eq $Γ (der_eq_cong_trefl _ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
  ↪ heq_trans
       (cong_refl
         (τ_eq $Γ $deqA)
         (heq_conj
           (heq_trans
             (convert $Γ $da1 (inv_eq_t1 (τ_dΓ $Γ) $deqa))
             (heq_trans
               (τ_eq $Γ $deqa)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqa) $da2)))
           (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da1) (inv_eq_t1 (τ_dΓ $Γ) $deqA))
           (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da2) (inv_eq_t2 (τ_dΓ $Γ) $deqA))))
       (heq_of_conversion $Γ
         (der_refl (τ_Γ $Γ) $s $a2 $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2)
         (der_eq_symm _ _ _ _ _ (der_eq_cong_teq (τ_Γ $Γ) $s $A1 $A2 $a1 $a2 $a1 $a2 $deqA $deqa $deqa $da1 $da2 $da1 $da2)))
with τ_eq $Γ (der_eq_cong_tuip _ $s $A1 $A2 $a1 $a2 $p1 $p2 $deqA $deqa $deqp $da1 $da2 $dp1 $dp2)
  ↪ heq_trans
       (heq_conj
         (cong_K
           (τ_eq $Γ $deqA)
           (heq_conj
             (heq_trans
               (convert $Γ $da1 (inv_eq_t1 (τ_dΓ $Γ) $deqa))
               (heq_trans
                 (τ_eq $Γ $deqa)
                 (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqa) $da2)))
             (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da1) (inv_eq_t1 (τ_dΓ $Γ) $deqA))
             (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da2) (inv_eq_t2 (τ_dΓ $Γ) $deqA)))
           (heq_conj
             (heq_trans
               (convert $Γ $dp1 (inv_eq_t1 (τ_dΓ $Γ) $deqp))
               (heq_trans
                 (τ_eq $Γ $deqp)
                 (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 (τ_dΓ $Γ) $deqp) $dp2)))
             (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dp1) (der_prop_type_eq (τ_Γ $Γ) $s $A1 $a1 $a1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) $da1 $da1))
             (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dp2) (der_prop_type_eq (τ_Γ $Γ) $s $A2 $a2 $a2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2 $da2))))
         (trans_eq_as_eq
           (transport
             (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dp1) (der_prop_type_eq (τ_Γ $Γ) $s $A1 $a1 $a1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) $da1 $da1))
             (τ $Γ $dp1))
           (eq_of_transport
             (refl (τ_s $s) (τ_T $Γ (inv_eq_t1 (τ_dΓ $Γ) $deqA)) (transport (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da1) (inv_eq_t1 (τ_dΓ $Γ) $deqA)) (τ $Γ $da1)))
             (convert_T $Γ
               (der_prop_type_eq (τ_Γ $Γ) $s $A1 $a1 $a1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) $da1 $da1)
               (der_prop_type_eq (τ_Γ $Γ) $s $A1 $a1 $a1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) $da1 $da1))))
         (trans_eq_as_eq
           (transport
             (convert_T $Γ (inv_sort (τ_dΓ $Γ) $dp2) (der_prop_type_eq (τ_Γ $Γ) $s $A2 $a2 $a2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2 $da2))
             (τ $Γ $dp2))
           (eq_of_transport
             (refl (τ_s $s) (τ_T $Γ (inv_eq_t2 (τ_dΓ $Γ) $deqA)) (transport (convert_T $Γ (inv_sort (τ_dΓ $Γ) $da2) (inv_eq_t2 (τ_dΓ $Γ) $deqA)) (τ $Γ $da2)))
             (convert_T $Γ
               (der_prop_type_eq (τ_Γ $Γ) $s $A2 $a2 $a2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2 $da2)
               (der_prop_type_eq (τ_Γ $Γ) $s $A2 $a2 $a2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2 $da2)))))
       (heq_of_conversion $Γ
         (der_uip (τ_Γ $Γ) $s $A2 $a2 $p2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2 $dp2)
         (der_eq_symm _ _ _ _ _
           (der_eq_cong_teq (τ_Γ $Γ) $s (ETT.teq $A1 $a1 $a1) (ETT.teq $A2 $a2 $a2) $p1 $p2 (ETT.trefl $A1 $a1) (ETT.trefl $A2 $a2)
             (der_eq_cong_teq (τ_Γ $Γ) $s $A1 $A2 $a1 $a2 $a1 $a2 $deqA $deqa $deqa $da1 $da2 $da1 $da2)
             $deqp (der_eq_cong_trefl (τ_Γ $Γ) $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
             $dp1 $dp2 (der_refl (τ_Γ $Γ) $s $a1 $A1 (inv_eq_t1 (τ_dΓ $Γ) $deqA) $da1) (der_refl (τ_Γ $Γ) $s $a2 $A2 (inv_eq_t2 (τ_dΓ $Γ) $deqA) $da2))))
;
