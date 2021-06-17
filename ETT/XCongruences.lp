
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.Inversions;

// Pair of contexts with equalities
// Extensional equivalent of PContext
constant symbol EqContext : TYPE;
symbol ec_to_ctx1 : EqContext → Context;
symbol ec_to_ctx2 : EqContext → Context;
symbol ec_to_dctx1 (ec : EqContext) : der_context (ec_to_ctx1 ec);
symbol ec_to_dctx2 (ec : EqContext) : der_context (ec_to_ctx2 ec);
symbol ec_get1 (ec : EqContext) (id : DBId) : der_eq (getΓ (ec_to_ctx1 ec) id)
                                                     (snext (getS (ec_to_ctx1 ec) id))
                                                     (tsort (getS (ec_to_ctx1 ec) id))
                                                     (get (ec_to_ctx1 ec) id)
                                                     (get (ec_to_ctx2 ec) id);
symbol ec_get2 (ec : EqContext) (id : DBId) : der_eq (getΓ (ec_to_ctx2 ec) id)
                                                     (snext (getS (ec_to_ctx1 ec) id))
                                                     (tsort (getS (ec_to_ctx1 ec) id))
                                                     (get (ec_to_ctx1 ec) id)
                                                     (get (ec_to_ctx2 ec) id);
constant symbol EC0 {Γ : Context} : der_context Γ → EqContext;
constant symbol ECPush {s : Sort} {T1 T2 : Term}
                       (ec : EqContext)
                       : der (ec_to_ctx1 ec) T1 (tsort s) (snext s)
                       → der (ec_to_ctx2 ec) T2 (tsort s) (snext s)
                       → der_eq (ec_to_ctx1 ec) (snext s) (tsort s) T1 T2
                       → EqContext;
rule ec_to_ctx1 (@EC0 $Γ _) ↪ $Γ
with ec_to_ctx1 (@ECPush $s $T1 _ $ec _ _ _) ↪ Push $T1 $s (ec_to_ctx1 $ec)
with ec_to_ctx2 (@EC0 $Γ _) ↪ $Γ
with ec_to_ctx2 (@ECPush $s _ $T2 $ec _ _ _) ↪ Push $T2 $s (ec_to_ctx2 $ec)
with getS (ec_to_ctx2 $ec) $id ↪ getS (ec_to_ctx1 $ec) $id;
rule ec_to_dctx1 (EC0 $dΓ) ↪ $dΓ
with ec_to_dctx1 (ECPush _ $d1 _ _) ↪ pushΓ $d1
with ec_to_dctx2 (EC0 $dΓ) ↪ $dΓ
with ec_to_dctx2 (ECPush _ _ $d2 _) ↪ pushΓ $d2;

// Convert in the context
symbol convert_der {s : Sort} {t A : Term}
                   (ec : EqContext)
                   : der (ec_to_ctx1 ec) t A s
                   → der (ec_to_ctx2 ec) t A s;
symbol convert_der_eq {s : Sort} {t1 t2 A : Term}
                      (ec : EqContext)
                      : der_eq (ec_to_ctx1 ec) s A t1 t2
                      → der_eq (ec_to_ctx2 ec) s A t1 t2;
symbol convert_der' {s : Sort} {t A : Term}
                    (ec : EqContext)
                    : der (ec_to_ctx2 ec) t A s
                    → der (ec_to_ctx1 ec) t A s;
symbol convert_der_eq' {s : Sort} {t1 t2 A : Term}
                       (ec : EqContext)
                       : der_eq (ec_to_ctx2 ec) s A t1 t2
                       → der_eq (ec_to_ctx1 ec) s A t1 t2;

rule ec_get1 (EC0 $dΓ) $id ↪ der_eq_refl _ _ _ _ (der_getΓ $id $dΓ)
with ec_get1 (ECPush _ _ _ $deq) db0 ↪ $deq
with ec_get1 (ECPush $ec _ _ _) (dbsucc $id) ↪ ec_get1 $ec $id
with ec_get2 (EC0 $dΓ) $id ↪ der_eq_refl _ _ _ _ (der_getΓ $id $dΓ)
with ec_get2 (ECPush $ec _ _ $deq) db0 ↪ convert_der_eq $ec $deq
with ec_get2 (ECPush $ec _ _ _) (dbsucc $id) ↪ ec_get2 $ec $id;

symbol pushEC {s : Sort} {A : Term}
              (ec : EqContext) (d : der (ec_to_ctx1 ec) A (tsort s) (snext s))
              : EqContext ≔
  ECPush ec d (convert_der ec d) (der_eq_refl _ _ _ _ d);
symbol pushEC' {s : Sort} {A : Term}
               (ec : EqContext) (d : der (ec_to_ctx2 ec) A (tsort s) (snext s))
               : EqContext ≔
  ECPush ec (convert_der' ec d) d (der_eq_refl _ _ _ _ (convert_der' ec d));

rule convert_der $ec (der_sort _ $s _)
  ↪ der_sort _ $s (ec_to_dctx2 $ec)
with convert_der $ec (der_prod _ $s $s' $A $B $dA $dB)
  ↪ der_prod _ $s $s' $A $B
              (convert_der $ec $dA)
              (convert_der (pushEC $ec $dA) $dB)
with convert_der $ec (der_sigma _ $s $s' $A $B $dA $dB)
  ↪ der_sigma _ $s $s' $A $B
               (convert_der $ec $dA)
               (convert_der (pushEC $ec $dA) $dB)
with convert_der $ec (der_prop_type_eq _ $s $A $u $v $dA $du $dv)
  ↪ der_prop_type_eq _ $s $A $u $v
                      (convert_der $ec $dA)
                      (convert_der $ec $du)
                      (convert_der $ec $dv)
with convert_der $ec (der_var _ $id _)
  ↪ der_type_conv _ _ _ _ _
                   (der_var _ $id (ec_to_dctx2 $ec))
                   (der_eq_symm _ _ _ _ _ (der_eq_shift $id (ec_to_dctx2 $ec) (ec_get2 $ec $id)))
with convert_der $ec (der_type_conv _ $u $A $B $s $du $deq)
  ↪ der_type_conv _ $u $A $B $s
                   (convert_der $ec $du)
                   (convert_der_eq $ec $deq)
with convert_der $ec (der_abs _ $s $s' $A $t $B $dA $dB $dt)
  ↪ der_abs _ $s $s' $A $t $B
             (convert_der $ec $dA)
             (convert_der (pushEC $ec $dA) $dB)
             (convert_der (pushEC $ec $dA) $dt)
with convert_der $ec (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du)
  ↪ der_app _ $s $s' $A $t $u $B
             (convert_der $ec $dA)
             (convert_der (pushEC $ec $dA) $dB)
             (convert_der $ec $dt)
             (convert_der $ec $du)
with convert_der $ec (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_pair _ $s $s' $u $A $v $B
              (convert_der $ec $dA)
              (convert_der $ec $du)
              (convert_der (pushEC $ec $dA) $dB)
              (convert_der $ec $dv)
with convert_der $ec (der_π1 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ der_π1 _ $s $s' $p $A $B
            (convert_der $ec $dA)
            (convert_der (pushEC $ec $dA) $dB)
            (convert_der $ec $dp)
with convert_der $ec (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ der_π2 _ $s $s' $p $A $B
            (convert_der $ec $dA)
            (convert_der (pushEC $ec $dA) $dB)
            (convert_der $ec $dp)
with convert_der $ec (der_refl _ $s $u $A $dA $du)
  ↪ der_refl _ $s $u $A
              (convert_der $ec $dA)
              (convert_der $ec $du)
with convert_der_eq $ec (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du)
  ↪ der_eq_beta _ $s $s' $u $A $t $B
                 (convert_der $ec $dA)
                 (convert_der (pushEC $ec $dA) $dB)
                 (convert_der (pushEC $ec $dA) $dt)
                 (convert_der $ec $du)
with convert_der_eq $ec (der_eq_eta _ $s $s' $A $f $B $dA $dB $df)
  ↪ der_eq_eta _ $s $s' $A $f $B
                (convert_der $ec $dA)
                (convert_der (pushEC $ec $dA) $dB)
                (convert_der $ec $df)
with convert_der_eq $ec (der_eq_π1 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π1 _ $s $s' $u $A $v $B
               (convert_der $ec $dA)
               (convert_der $ec $du)
               (convert_der (pushEC $ec $dA) $dB)
               (convert_der $ec $dv)
with convert_der_eq $ec (der_eq_π2 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π2 _ $s $s' $u $A $v $B
               (convert_der $ec $dA)
               (convert_der $ec $du)
               (convert_der (pushEC $ec $dA) $dB)
               (convert_der $ec $dv)
with convert_der_eq $ec (der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deqt $deqT)
  ↪ der_eq_conversion _ $s $t1 $t2 $T1 $T2
                       (convert_der_eq $ec $deqt)
                       (convert_der_eq $ec $deqT)
with convert_der_eq $ec (der_eq_lift _ $s $e $u $v $A $de)
  ↪ der_eq_lift _ $s $e $u $v $A
                 (convert_der $ec $de)
with convert_der_eq $ec (der_eq_refl _ $s $u $A $du)
  ↪ der_eq_refl _ $s $u $A (convert_der $ec $du)
with convert_der_eq $ec (der_eq_trans _ $s $u $v $w $A $duv $dvw)
  ↪ der_eq_trans _ $s $u $v $w $A
                  (convert_der_eq $ec $duv)
                  (convert_der_eq $ec $dvw)
with convert_der_eq $ec (der_eq_symm _ $s $u $v $A $duv)
  ↪ der_eq_symm _ $s $u $v $A (convert_der_eq $ec $duv)
with convert_der_eq $ec (der_eq_cong_tfun _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tfun _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dB2)
with convert_der_eq $ec (der_eq_cong_tabs _ _ _ _ _ _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ der_eq_cong_tabs _ _ _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqt)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dt1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dt2)
with convert_der_eq $ec (der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
  ↪ der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq $ec $deqf)
       (convert_der_eq $ec $deqa)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der $ec $df1) (convert_der $ec $df2)
       (convert_der $ec $da1) (convert_der $ec $da2)
with convert_der_eq $ec (der_eq_cong_tsum _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tsum _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dB2)
with convert_der_eq $ec (der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq $ec $deqa)
       (convert_der_eq $ec $deqb)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der $ec $da1) (convert_der $ec $da2)
       (convert_der $ec $db1) (convert_der $ec $db2)
with convert_der_eq $ec (der_eq_cong_π1 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π1 _ _ _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq $ec $deqp)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der $ec $dp1) (convert_der $ec $dp2)
with convert_der_eq $ec (der_eq_cong_π2 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π2 _ _ _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq (pushEC $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq $ec $deqp)
       (convert_der (pushEC $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der (pushEC $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der $ec $dp1) (convert_der $ec $dp2)
with convert_der_eq $ec (der_eq_cong_teq _ _ _ _ _ _ _ _ $deqA $deqa $deqb $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_teq _ _ _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq $ec $deqa)
       (convert_der_eq $ec $deqb)
       (convert_der $ec $da1) (convert_der $ec $da2)
       (convert_der $ec $db1) (convert_der $ec $db2)
with convert_der_eq $ec (der_eq_cong_trefl _ _ _ _ _ _ $deqA $deqa $da1 $da2)
  ↪ der_eq_cong_trefl _ _ _ _ _ _
       (convert_der_eq $ec $deqA)
       (convert_der_eq $ec $deqa)
       (convert_der $ec $da1) (convert_der $ec $da2)
;

rule convert_der' $ec (der_sort _ $s _)
  ↪ der_sort _ $s (ec_to_dctx1 $ec)
with convert_der' $ec (der_prod _ $s $s' $A $B $dA $dB)
  ↪ der_prod _ $s $s' $A $B
              (convert_der' $ec $dA)
              (convert_der' (pushEC' $ec $dA) $dB)
with convert_der' $ec (der_sigma _ $s $s' $A $B $dA $dB)
  ↪ der_sigma _ $s $s' $A $B
               (convert_der' $ec $dA)
               (convert_der' (pushEC' $ec $dA) $dB)
with convert_der' $ec (der_prop_type_eq _ $s $A $u $v $dA $du $dv)
  ↪ der_prop_type_eq _ $s $A $u $v
                      (convert_der' $ec $dA)
                      (convert_der' $ec $du)
                      (convert_der' $ec $dv)
with convert_der' $ec (der_var _ $id _)
  ↪ der_type_conv _ _ _ _ _
                   (der_var _ $id (ec_to_dctx1 $ec))
                   (der_eq_shift $id (ec_to_dctx1 $ec) (ec_get1 $ec $id))
with convert_der' $ec (der_type_conv _ $u $A $B $s $du $deq)
  ↪ der_type_conv _ $u $A $B $s
                   (convert_der' $ec $du)
                   (convert_der_eq' $ec $deq)
with convert_der' $ec (der_abs _ $s $s' $A $t $B $dA $dB $dt)
  ↪ der_abs _ $s $s' $A $t $B
             (convert_der' $ec $dA)
             (convert_der' (pushEC' $ec $dA) $dB)
             (convert_der' (pushEC' $ec $dA) $dt)
with convert_der' $ec (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du)
  ↪ der_app _ $s $s' $A $t $u $B
             (convert_der' $ec $dA)
             (convert_der' (pushEC' $ec $dA) $dB)
             (convert_der' $ec $dt)
             (convert_der' $ec $du)
with convert_der' $ec (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_pair _ $s $s' $u $A $v $B
              (convert_der' $ec $dA)
              (convert_der' $ec $du)
              (convert_der' (pushEC' $ec $dA) $dB)
              (convert_der' $ec $dv)
with convert_der' $ec (der_π1 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ der_π1 _ $s $s' $p $A $B
            (convert_der' $ec $dA)
            (convert_der' (pushEC' $ec $dA) $dB)
            (convert_der' $ec $dp)
with convert_der' $ec (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ der_π2 _ $s $s' $p $A $B
            (convert_der' $ec $dA)
            (convert_der' (pushEC' $ec $dA) $dB)
            (convert_der' $ec $dp)
with convert_der' $ec (der_refl _ $s $u $A $dA $du)
  ↪ der_refl _ $s $u $A
              (convert_der' $ec $dA)
              (convert_der' $ec $du)
with convert_der_eq' $ec (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du)
  ↪ der_eq_beta _ $s $s' $u $A $t $B
                 (convert_der' $ec $dA)
                 (convert_der' (pushEC' $ec $dA) $dB)
                 (convert_der' (pushEC' $ec $dA) $dt)
                 (convert_der' $ec $du)
with convert_der_eq' $ec (der_eq_eta _ $s $s' $A $f $B $dA $dB $df)
  ↪ der_eq_eta _ $s $s' $A $f $B
                (convert_der' $ec $dA)
                (convert_der' (pushEC' $ec $dA) $dB)
                (convert_der' $ec $df)
with convert_der_eq' $ec (der_eq_π1 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π1 _ $s $s' $u $A $v $B
               (convert_der' $ec $dA)
               (convert_der' $ec $du)
               (convert_der' (pushEC' $ec $dA) $dB)
               (convert_der' $ec $dv)
with convert_der_eq' $ec (der_eq_π2 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π2 _ $s $s' $u $A $v $B
               (convert_der' $ec $dA)
               (convert_der' $ec $du)
               (convert_der' (pushEC' $ec $dA) $dB)
               (convert_der' $ec $dv)
with convert_der_eq' $ec (der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deqt $deqT)
  ↪ der_eq_conversion _ $s $t1 $t2 $T1 $T2
                       (convert_der_eq' $ec $deqt)
                       (convert_der_eq' $ec $deqT)
with convert_der_eq' $ec (der_eq_lift _ $s $e $u $v $A $de)
  ↪ der_eq_lift _ $s $e $u $v $A
                 (convert_der' $ec $de)
with convert_der_eq' $ec (der_eq_refl _ $s $u $A $du)
  ↪ der_eq_refl _ $s $u $A (convert_der' $ec $du)
with convert_der_eq' $ec (der_eq_trans _ $s $u $v $w $A $duv $dvw)
  ↪ der_eq_trans _ $s $u $v $w $A
                  (convert_der_eq' $ec $duv)
                  (convert_der_eq' $ec $dvw)
with convert_der_eq' $ec (der_eq_symm _ $s $u $v $A $duv)
  ↪ der_eq_symm _ $s $u $v $A (convert_der_eq' $ec $duv)
with convert_der_eq' $ec (der_eq_cong_tfun _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tfun _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dB2)
with convert_der_eq' $ec (der_eq_cong_tabs _ _ _ _ _ _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ der_eq_cong_tabs _ _ _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqt)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dt1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dt2)
with convert_der_eq' $ec (der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
  ↪ der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq' $ec $deqf)
       (convert_der_eq' $ec $deqa)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der' $ec $df1) (convert_der' $ec $df2)
       (convert_der' $ec $da1) (convert_der' $ec $da2)
with convert_der_eq' $ec (der_eq_cong_tsum _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tsum _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dB2)
with convert_der_eq' $ec (der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq' $ec $deqa)
       (convert_der_eq' $ec $deqb)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der' $ec $da1) (convert_der' $ec $da2)
       (convert_der' $ec $db1) (convert_der' $ec $db2)
with convert_der_eq' $ec (der_eq_cong_π1 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π1 _ _ _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq' $ec $deqp)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der' $ec $dp1) (convert_der' $ec $dp2)
with convert_der_eq' $ec (der_eq_cong_π2 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π2 _ _ _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' (pushEC' $ec (inv_eq_t1 $deqA)) $deqB)
       (convert_der_eq' $ec $deqp)
       (convert_der' (pushEC' $ec (inv_eq_t1 $deqA)) $dB1)
       (convert_der' (pushEC' $ec (inv_eq_t2 $deqA)) $dB2)
       (convert_der' $ec $dp1) (convert_der' $ec $dp2)
with convert_der_eq' $ec (der_eq_cong_teq _ _ _ _ _ _ _ _ $deqA $deqa $deqb $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_teq _ _ _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' $ec $deqa)
       (convert_der_eq' $ec $deqb)
       (convert_der' $ec $da1) (convert_der' $ec $da2)
       (convert_der' $ec $db1) (convert_der' $ec $db2)
with convert_der_eq' $ec (der_eq_cong_trefl _ _ _ _ _ _ $deqA $deqa $da1 $da2)
  ↪ der_eq_cong_trefl _ _ _ _ _ _
       (convert_der_eq' $ec $deqA)
       (convert_der_eq' $ec $deqa)
       (convert_der' $ec $da1) (convert_der' $ec $da2)
;
