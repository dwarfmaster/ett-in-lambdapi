
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.Packing;
require open ETT.TranslationDefinition;
require open ETT.Congruences;
require open ETT.TranslationLemmas;
require open ETT.TContext;
require open ETT.Translation;

// Translation of product
symbol τ_fun_heq (Γ : TContext) (s s' : ETT.Sort) (A B T : ETT.Term)
                 (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                 (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                 (df : der (τ_Γ Γ) (ETT.tfun A B) T (ETT.snext (ETT.smax s s')))
                 : H (τ Γ df)
                     (P (τ_s s) (τ_s s') (τ Γ dA) (λ a, τ (TPush Γ s A dA a) dB));
rule @τ_fun_eq $Γ $s $s' $A $B $dA $dB $df
  ↪ heq_to_eq (τ_fun_heq $Γ $s $s' $A $B (ETT.tsort (ETT.smax $s $s')) $dA $dB $df);

rule τ_fun_heq $Γ $s $s' $A $B _ $dA $dB (der_prod _ $s $s' $A $B $dA' $dB')
  ↪ cong_prod
       (λ a, τ (TPush $Γ $s $A $dA' a) $dB')
       (λ a, τ (TPush $Γ $s $A $dA  a) $dB)
       (convert $Γ $dA' $dA)
       (λ p, convertR $Γ (PCPush (PCEmpty $Γ) $dA' $dA (projHEq p)) $dB' $dB)
with τ_fun_heq $Γ $s $s' $A $B $T $dA $dB (der_type_conv _ (ETT.tfun $A $B) $U $T (ETT.snext (ETT.smax $s $s')) $du $deq)
  ↪ heq_trans
       (heq_symm (heq_trans
         (heq_of_transport (τ $Γ $du) (convert_T $Γ (inv_sort $du) (inv_eq_t1 $deq)))
         (heq_of_transport
           (transport (convert_T $Γ (inv_sort $du) (inv_eq_t1 $deq)) (τ $Γ $du))
           (τ_eqT $Γ $deq))))
       (τ_fun_heq $Γ $s $s' $A $B $U $dA $dB $du);

// Translation of sum
symbol τ_sum_heq (Γ : TContext) (s s' : ETT.Sort) (A B T : ETT.Term)
                 (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                 (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                 (dp : der (τ_Γ Γ) (ETT.tsum A B) T (ETT.snext (ETT.smax s s')))
                 : H (τ Γ dp)
                     (S (τ_s s) (τ_s s') (τ Γ dA) (λ a, τ (TPush Γ s A dA a) dB));
rule @τ_sum_eq $Γ $s $s' $A $B $dA $dB $dp
  ↪ heq_to_eq (τ_sum_heq $Γ $s $s' $A $B (ETT.tsort (ETT.smax $s $s')) $dA $dB $dp);

rule τ_sum_heq $Γ $s $s' $A $B _ $dA $dB (der_sigma _ $s $s' $A $B $dA' $dB')
  ↪ cong_sum
       (λ a, τ (TPush $Γ $s $A $dA' a) $dB')
       (λ a, τ (TPush $Γ $s $A $dA  a) $dB)
       (convert $Γ $dA' $dA)
       (λ p, convertR $Γ (PCPush (PCEmpty $Γ) $dA' $dA (projHEq p)) $dB' $dB)
with τ_sum_heq $Γ $s $s' $A $B $T $dA $dB (der_type_conv _ (ETT.tsum $A $B) $U $T (ETT.snext (ETT.smax $s $s')) $du $deq)
  ↪ heq_trans
       (heq_symm (heq_trans
         (heq_of_transport (τ $Γ $du) (convert_T $Γ (inv_sort $du) (inv_eq_t1 $deq)))
         (heq_of_transport
           (transport (convert_T $Γ (inv_sort $du) (inv_eq_t1 $deq)) (τ $Γ $du))
           (τ_eqT $Γ $deq))))
       (τ_sum_heq $Γ $s $s' $A $B $U $dA $dB $du);

// Translation of equality
symbol τ_equality_heq (Γ : TContext) (s : ETT.Sort) (A a a' T : ETT.Term)
                      (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                      (da : der (τ_Γ Γ) a A s) (da' : der (τ_Γ Γ) a' A s)
                      (de : der (τ_Γ Γ) (ETT.teq A a a') T (ETT.snext s))
                      : H (τ Γ de)
                          (eq (τ_s s) (τ Γ dA)
                              (transport (convert_T Γ (inv_sort da ) dA) (τ Γ da))
                              (transport (convert_T Γ (inv_sort da') dA) (τ Γ da')));
rule @τ_equality_eq $Γ $s $A $a $a' $dA $da $da' $de
  ↪ heq_to_eq (τ_equality_heq $Γ $s $A $a $a' (ETT.tsort $s) $dA $da $da' $de);

rule τ_equality_heq $Γ $s $A $a1 $a2 _ $dA $da1 $da2 (der_prop_type_eq _ $s $A $a1 $a2 $dA' $da1' $da2')
  ↪ cong_eq
       (convert $Γ $dA' $dA)
       (heq_conj (convert $Γ $da1' $da1)
         (convert_T $Γ (inv_sort $da1') $dA')
         (convert_T $Γ (inv_sort $da1 ) $dA))
       (heq_conj (convert $Γ $da2' $da2)
         (convert_T $Γ (inv_sort $da2') $dA')
         (convert_T $Γ (inv_sort $da2 ) $dA))
with τ_equality_heq $Γ $s $A $a1 $a2 $T $dA $da1 $da2 (der_type_conv _ (ETT.teq $A $a1 $a2) $U $T (ETT.snext $s) $du $deq)
  ↪ heq_trans
       (heq_symm (heq_trans
         (heq_of_transport (τ $Γ $du) (convert_T $Γ (inv_sort $du) (inv_eq_t1 $deq)))
         (heq_of_transport
           (transport (convert_T $Γ (inv_sort $du) (inv_eq_t1 $deq)) (τ $Γ $du))
           (τ_eqT $Γ $deq))))
       (τ_equality_heq $Γ $s $A $a1 $a2 $U $dA $da1 $da2 $du);
