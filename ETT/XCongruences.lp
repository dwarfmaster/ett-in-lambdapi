
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
with ec_to_ctx2 (@ECPush $s _ $T2 $ec _ _ _) ↪ Push $T2 $s (ec_to_ctx2 $ec);

// Convert in the context
// TODO convert_der
symbol convert_der {s : Sort} {t A : Term}
                   (ec : EqContext)
                   : der (ec_to_ctx1 ec) t A s
                   → der (ec_to_ctx2 ec) t A s;
// TODO convert_der'
symbol convert_der' {s : Sort} {t A : Term}
                    (ec : EqContext)
                    : der (ec_to_ctx2 ec) t A s
                    → der (ec_to_ctx1 ec) t A s;

