
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;

builtin "0" ≔ db0;
builtin "+1" ≔ dbsucc;

symbol funext (s s' : Sort) : Term ≔
  tfun (tsort s) // A
  (tfun (tfun (var 0) (tsort s')) // B
  (tfun (tfun (var 1) (var 1)) // f
  (tfun (tfun (var 2) (var 2)) // g
  (tfun (tfun (var 2)
              (teq (var 3)
                   (tapp (var 4) (var 3) (var 2) (var 0))
                   (tapp (var 4) (var 3) (var 1) (var 0)))) // Π x, f x = g x
        (teq (tfun (var 4) (var 3)) (var 2) (var 1)))))); // f = g
