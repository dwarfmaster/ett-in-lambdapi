
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
// TODO ec_to_dctx1
symbol ec_to_dctx1 (ec : EqContext) : der_context (ec_to_ctx1 ec);
// TODO ec_to_dctx2
symbol ec_to_dctx2 (ec : EqContext) : der_context (ec_to_ctx2 ec);
// TODO ec_get1
symbol ec_get1 (ec : EqContext) (id : DBId) : der_eq (getΓ (ec_to_ctx1 ec) id)
                                                     (snext (getS (ec_to_ctx1 ec) id))
                                                     (tsort (getS (ec_to_ctx1 ec) id))
                                                     (get (ec_to_ctx1 ec) id)
                                                     (get (ec_to_ctx2 ec) id);
// TODO ec_get2
symbol ec_get2 (ec : EqContext) (id : DBId) : der_eq (getΓ (ec_to_ctx2 ec) id)
                                                     (snext (getS (ec_to_ctx1 ec) id))
                                                     (tsort (getS (ec_to_ctx1 ec) id))
                                                     (get (ec_to_ctx1 ec) id)
                                                     (get (ec_to_ctx2 ec) id);
constant symbol EC0 : Context → EqContext;
constant symbol ECPush {s : Sort} {T1 T2 : Term}
                       (ec : EqContext)
                       : der (ec_to_ctx1 ec) T1 (tsort s) (snext s)
                       → der (ec_to_ctx2 ec) T2 (tsort s) (snext s)
                       → der_eq (ec_to_ctx1 ec) (snext s) (tsort s) T1 T2
                       → EqContext;
rule ec_to_ctx1 (EC0 $Γ) ↪ $Γ
with ec_to_ctx1 (@ECPush $s $T1 _ $ec _ _ _) ↪ Push $T1 $s (ec_to_ctx1 $ec)
with ec_to_ctx2 (EC0 $Γ) ↪ $Γ
with ec_to_ctx2 (@ECPush $s _ $T2 $ec _ _ _) ↪ Push $T2 $s (ec_to_ctx2 $ec)
with getS (ec_to_ctx2 $ec) $id ↪ getS (ec_to_ctx1 $ec) $id;

// Convert in the context
symbol convert_der {s : Sort} {t A : Term}
                   (ec : EqContext)
                   : der (ec_to_ctx1 ec) t A s
                   → der (ec_to_ctx2 ec) t A s;
// TODO convert_der_eq
symbol convert_der_eq {s : Sort} {t1 t2 A : Term}
                      (ec : EqContext)
                      : der_eq (ec_to_ctx1 ec) s A t1 t2
                      → der_eq (ec_to_ctx2 ec) s A t1 t2;
// TODO convert_der'
symbol convert_der' {s : Sort} {t A : Term}
                    (ec : EqContext)
                    : der (ec_to_ctx2 ec) t A s
                    → der (ec_to_ctx1 ec) t A s;

symbol pushEC {s : Sort} {A : Term}
              (ec : EqContext) (d : der (ec_to_ctx1 ec) A (tsort s) (snext s))
              : EqContext ≔
  ECPush ec d (convert_der ec d) (der_eq_refl _ _ _ _ d);

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
;
