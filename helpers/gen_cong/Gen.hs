{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

import Data.Text.Lazy.Builder
import System.Environment
import qualified Data.Map as M
import qualified Data.Text.Lazy.IO as TIO

data Sort = S0
          | SSucc Sort
          | SVar String
          | SMax Sort Sort
instance Show Sort where
  show S0           = "s0"
  show (SSucc s)    = "(snext " <> show s <> ")"
  show (SVar s)     = s
  show (SMax s1 s2) = "(smax " <> show s1 <> " " <> show s2 <> ")"

data Arg = Simple Sort
         | Dep Int Sort
         | Term Int Int

data AccT = AccT
          { sort :: Sort
          , val  :: String
          , orig :: String
          }

genIType :: ([String] -> String) -> [(Arg,String)] -> [AccT] -> Builder
genIType typef [] acc = "H' (" <> (fromString $ typef $ fmap orig acc) <> ") (" <> (fromString $ typef $ fmap val acc) <> ")"
genIType typef ((Simple s, name) : tl) acc =
  "P _ _ (u " <> (fromString $ show s) <> ") "
  <> "(λ " <> (fromString name) <> ", P _ _ (H' " <> fromString name <> "1 " <> fromString name <> ") "
  <> "(" <> genIType typef tl (AccT s name (name <> "1") : acc) <> "))"
genIType typef ((Dep d s, name) : tl) acc =
  "P _ _ (P _ _ " <> (fromString $ val $ acc !! d) <> " (λ _, u " <> (fromString $ show s) <> ")) "
  <> "(λ " <> (fromString name) <> ", P _ _ "
     <> "(P _ _ (Pack' " <> (fromString $ orig $ acc !! d) <> " " <> (fromString $ val$ acc !! d) <> ") "
     <> "(λ p, H' (" <> fromString name <> "1 (projT1 p)) (" <> fromString name <> " (projT2 p)))) "
  <> "(" <> genIType typef tl (AccT s name (name <> "1") : acc) <> "))"
genIType _ _ _ = "UNIMPLEMENTED"

genCong :: ([String] -> String) -> [(Arg,String)] -> [AccT] -> Builder
genCong typef [] acc = "(heq_refl _ (" <> (fromString $ typef $ fmap val acc) <> ")"
genCong typef ((Simple s, name) : tl) acc =
  let t = fromString name :: Builder in
  let hT = fromString ('h' : name) :: Builder in
    "(λ _ " <> hT <> ", rewr (heq_to_eq " <> hT <> ")\n"
    <> "  (λ " <> t <> ", " <> genIType typef tl (AccT s name (name <> "1") : acc) <> ")\n"
    <> genCong typef tl (AccT s (name <> "1") (name <> "1") : acc) <> ")"
genCong typef ((Dep d s, name) : tl) acc =
  let t = fromString name :: Builder in
  let hT = fromString ('h' : name) :: Builder in
  let a = AccT (SMax (sort $ acc !! d) s) name (name <> "1") in
    "(λ _ " <> hT <> ", rewr (packExt " <> fromString name <> "1 " <> t <> " " <> hT <> ")\n"
    <> "  (λ " <> t <> ", " <> genIType typef tl (a : acc) <> ")\n"
    <> genCong typef tl (a : acc) <> ")"
genCong _ ((Term _ _, _) : _) _ = "UNIMPLEMENTED"

generators :: M.Map String ([(Arg,String)],[String] -> String)
generators = M.fromList
           [ ("prod", ([(Simple (SVar "s"), "A"), (Dep 0 (SVar "s'"), "B")], \[b, a] -> "P s s' " <> a <> " " <> b))
           ]

main :: IO ()
main = getArgs >>= \case
  [] -> putStrLn "Expected one argument"
  arg : _ -> (case M.lookup arg generators of
               Nothing -> putStrLn $ "Constructor " <> arg <> " not defined"
               Just (args,typef) -> TIO.putStrLn $ toLazyText $ genCong typef args [])
