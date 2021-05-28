
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

// Helper
symbol heq_of_conversion (Γ : TContext) {s : ETT.Sort} {a A B : ETT.Term}
                         (da : der (τ_Γ Γ) a A s) (deq : der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) A B)
                         : H (τ Γ da) (τ Γ (der_type_conv (τ_Γ Γ) a A B s da deq)) ≔
  heq_trans
   (heq_of_transport (τ Γ da) (convert_T Γ (inv_sort da) (inv_eq_t1 deq)))
   (heq_of_transport (transport (convert_T Γ (inv_sort da) (inv_eq_t1 deq)) (τ Γ da)) (τ_eqT Γ deq));

// Lambda calculus
rule τ_eq $Γ (der_eq_cong_tfun _ $s _ $A1 $A2 _ _ $deqA $deqB $dB1 $dB2)
  ↪ cong_prod
       (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) $dB1)
       (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) $dB2)
       (τ_eq $Γ $deqA)
       (λ p, heq_trans
         (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $dB1 (inv_eq_t1 $deqB))
         (heq_trans
           (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqB)
           (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqB) $dB2)))
with τ_eq $Γ (der_eq_cong_tabs _ $s $s' $A1 $A2 $B1 $B2 _ $t2 $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ heq_trans
       (cong_lambda
         (λ a, τ_T (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) (inv_sort $dt1))
         (λ a, τ_T (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) (inv_sort $dt2))
         (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) $dt1)
         (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) $dt2)
         (τ_eq $Γ $deqA)
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) (inv_sort $dt1) (inv_eq_t1 $deqB))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqB)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqB) (inv_sort $dt2))))
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $dt1 (inv_eq_t1 $deqt))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqt)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqt) $dt2))))
       (heq_of_conversion $Γ
         (der_abs (τ_Γ $Γ) $s $s' $A2 $t2 $B2 (inv_eq_t2 $deqA) $dB2 $dt2)
         (der_eq_symm _ _ _ _ _ (der_eq_cong_tfun (τ_Γ $Γ) $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)))
with τ_eq $Γ (der_eq_cong_tapp _ $s $s' $A1 $A2 _ $B2 _ $f2 _ $a2 $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
  ↪ heq_trans
       (heq_conj
         (cong_app
           (λ a, τ (TPush $Γ $s $A1 (inv_sort $da1) a) $dB1)
           (λ a, τ (TPush $Γ $s $A2 (inv_sort $da2) a) $dB2)
           (heq_trans
             (convert $Γ (inv_sort $da1) (inv_eq_t1 $deqA))
             (heq_trans
               (τ_eq $Γ $deqA)
               (convert $Γ (inv_eq_t2 $deqA) (inv_sort $da2))))
           (λ p, heq_trans
             (convert (TPush $Γ $s $A1 (inv_sort $da1) (projT1 p)) $dB1 (inv_eq_t1 $deqB))
             (heq_trans
               (τ_eq (TPush $Γ $s $A1 (inv_sort $da1) (projT1 p)) $deqB)
               (convertR $Γ (PCPush (PCEmpty $Γ) (inv_sort $da1) (inv_sort $da2) (projHEq p)) (inv_eq_t2 $deqB) $dB2)))
           (heq_conj
             (heq_trans
               (convert $Γ $df1 (inv_eq_t1 $deqf))
               (heq_trans
                 (τ_eq $Γ $deqf)
                 (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqf) $df2)))
             (τ_fun_eq $Γ (inv_sort $da1) $dB1 (inv_sort $df1))
             (τ_fun_eq $Γ (inv_sort $da2) $dB2 (inv_sort $df2)))
           (heq_trans
             (convert $Γ $da1 (inv_eq_t1 $deqa))
             (heq_trans
               (τ_eq $Γ $deqa)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqa) $da2))))
         (τ_substT_eq $Γ $dB1 $da1)
         (τ_substT_eq $Γ $dB2 $da2))
       (heq_of_conversion $Γ
         (der_app (τ_Γ $Γ) $s $s' $A2 $f2 $a2 $B2 (inv_eq_t2 $deqA) $dB2 $df2 $da2)
         (der_eq_symm _ _ _ _ _ (der_eq_cong_apply (τ_Γ $Γ) $deqA $deqB $deqa $dB1 $dB2 $da1 $da2)))

// Pairs
with τ_eq $Γ (der_eq_cong_tsum _ $s _ $A1 $A2 _ _ $deqA $deqB $dB1 $dB2)
  ↪ cong_sum
       (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) $dB1)
       (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) $dB2)
       (τ_eq $Γ $deqA)
       (λ p, heq_trans
         (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $dB1 (inv_eq_t1 $deqB))
         (heq_trans
           (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqB)
           (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqB) $dB2)))
with τ_eq $Γ (der_eq_cong_tpair _ $s $s' $A1 $A2 $B1 $B2 _ $a2 _ $b2 $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
  ↪ heq_trans
         (cong_pair
           (λ a, τ (TPush $Γ $s $A1 (inv_sort $da1) a) $dB1)
           (λ a, τ (TPush $Γ $s $A2 (inv_sort $da2) a) $dB2)
           (heq_trans
             (convert $Γ (inv_sort $da1) (inv_eq_t1 $deqA))
             (heq_trans
               (τ_eq $Γ $deqA)
               (convert $Γ (inv_eq_t2 $deqA) (inv_sort $da2))))
           (λ p, heq_trans
             (convert (TPush $Γ $s $A1 (inv_sort $da1) (projT1 p)) $dB1 (inv_eq_t1 $deqB))
             (heq_trans
               (τ_eq (TPush $Γ $s $A1 (inv_sort $da1) (projT1 p)) $deqB)
               (convertR $Γ (PCPush (PCEmpty $Γ) (inv_sort $da1) (inv_sort $da2) (projHEq p)) (inv_eq_t2 $deqB) $dB2)))
           (heq_trans
             (convert $Γ $da1 (inv_eq_t1 $deqa))
             (heq_trans
               (τ_eq $Γ $deqa)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqa) $da2)))
           (heq_conj
             (heq_conj
               (heq_trans
                 (convert $Γ $db1 (inv_eq_t1 $deqb))
                 (heq_trans
                   (τ_eq $Γ $deqb)
                   (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqb) $db2)))
               (convert_T $Γ (inv_sort $db1) (substitution $dB1 $da1))
               (convert_T $Γ (inv_sort $db2) (substitution $dB2 $da2)))
             (inv_eq (τ_substT_eq $Γ $dB1 $da1))
             (inv_eq (τ_substT_eq $Γ $dB2 $da2))))
         (heq_of_conversion $Γ
           (der_pair (τ_Γ $Γ) $s $s' $a2 $A2 $b2 $B2 (inv_eq_t2 $deqA) $da2 $dB2 $db2)
           (der_eq_symm _ _ _ _ _ (der_eq_cong_tsum (τ_Γ $Γ) $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)))
with τ_eq $Γ (der_eq_cong_π1 _ $s $s' $A1 $A2 _ $B2 _ $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ heq_trans
       (cong_proj1
         (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) $dB1)
         (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) $dB2)
         (τ_eq $Γ $deqA)
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $dB1 (inv_eq_t1 $deqB))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqB)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqB) $dB2)))
         (heq_conj
           (heq_trans
             (convert $Γ $dp1 (inv_eq_t1 $deqp))
             (heq_trans
               (τ_eq $Γ $deqp)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqp) $dp2)))
           (τ_sum_eq $Γ (inv_eq_t1 $deqA) $dB1 (inv_sort $dp1))
           (τ_sum_eq $Γ (inv_eq_t2 $deqA) $dB2 (inv_sort $dp2))))
       (heq_of_conversion $Γ
         (der_π1 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 $deqA) $dB2 $dp2)
         (der_eq_symm _ _ _ _ _ $deqA))
with τ_eq $Γ (der_eq_cong_π2 _ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ heq_trans
       (heq_conj
         (cong_proj2
           (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) $dB1)
           (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) $dB2)
           (τ_eq $Γ $deqA)
           (λ p, heq_trans
             (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $dB1 (inv_eq_t1 $deqB))
             (heq_trans
               (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqB)
               (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqB) $dB2)))
           (heq_conj
             (heq_trans
               (convert $Γ $dp1 (inv_eq_t1 $deqp))
               (heq_trans
                 (τ_eq $Γ $deqp)
                 (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqp) $dp2)))
             (τ_sum_eq $Γ (inv_eq_t1 $deqA) $dB1 (inv_sort $dp1))
             (τ_sum_eq $Γ (inv_eq_t2 $deqA) $dB2 (inv_sort $dp2))))
         (τ_substT_eq $Γ $dB1 (der_π1 (τ_Γ $Γ) $s $s' $p1 $A1 $B1 (inv_eq_t1 $deqA) $dB1 $dp1))
         (τ_substT_eq $Γ $dB2 (der_π1 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 $deqA) $dB2 $dp2)))
       (heq_of_conversion $Γ
         (der_π2 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 $deqA) $dB2 $dp2)
         (der_eq_symm _ _ _ _ _
          (der_eq_cong_apply (τ_Γ $Γ) $deqA $deqB
           (der_eq_cong_π1 (τ_Γ $Γ) $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
           $dB1 $dB2
           (der_π1 (τ_Γ $Γ) $s $s' $p1 $A1 $B1 (inv_eq_t1 $deqA) $dB1 $dp1)
           (der_π1 (τ_Γ $Γ) $s $s' $p2 $A2 $B2 (inv_eq_t2 $deqA) $dB2 $dp2))))

// Equalities
with τ_eq $Γ (der_eq_cong_teq _ _ _ _ _ _ _ _ $deqA $deqa $deqb $da1 $da2 $db1 $db2)
  ↪ cong_eq
       (τ_eq $Γ $deqA)
       (heq_conj
         (heq_trans
           (convert $Γ $da1 (inv_eq_t1 $deqa))
           (heq_trans
             (τ_eq $Γ $deqa)
             (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqa) $da2)))
         (convert_T $Γ (inv_sort $da1) (inv_eq_t1 $deqA))
         (convert_T $Γ (inv_sort $da2) (inv_eq_t2 $deqA)))
       (heq_conj
         (heq_trans
           (convert $Γ $db1 (inv_eq_t1 $deqb))
           (heq_trans
             (τ_eq $Γ $deqb)
             (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqb) $db2)))
         (convert_T $Γ (inv_sort $db1) (inv_eq_t1 $deqA))
         (convert_T $Γ (inv_sort $db2) (inv_eq_t2 $deqA)))
with τ_eq $Γ (der_eq_cong_trefl _ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
  ↪ heq_trans
       (cong_refl
         (τ_eq $Γ $deqA)
         (heq_conj
           (heq_trans
             (convert $Γ $da1 (inv_eq_t1 $deqa))
             (heq_trans
               (τ_eq $Γ $deqa)
               (convertR $Γ (PCEmpty $Γ) (inv_eq_t2 $deqa) $da2)))
           (convert_T $Γ (inv_sort $da1) (inv_eq_t1 $deqA))
           (convert_T $Γ (inv_sort $da2) (inv_eq_t2 $deqA))))
       (heq_of_conversion $Γ
         (der_refl (τ_Γ $Γ) $s $a2 $A2 (inv_eq_t2 $deqA) $da2)
         (der_eq_symm _ _ _ _ _ (der_eq_cong_teq (τ_Γ $Γ) $s $A1 $A2 $a1 $a2 $a1 $a2 $deqA $deqa $deqa $da1 $da2 $da1 $da2)))
;
