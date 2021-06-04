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
          { val  :: String
          , orig :: String
          }

genIType :: ([String] -> String) -> ([String] -> String) -> [(Arg,String)] -> [AccT] -> Builder
genIType termf typef [] acc = "HEq' _ "
                           <> (fromString $ typef $ fmap orig acc) <> " "
                           <> (fromString $ typef $ fmap val acc)  <> " "
                           <> (fromString $ termf $ fmap orig acc) <> " "
                           <> (fromString $ termf $ fmap val acc)
genIType termf typef ((Simple s, name) : tl) acc =
  "P _ _ (u " <> (fromString $ show s) <> ") "
  <> "(λ " <> (fromString name) <> ", P _ _ (H' " <> fromString name <> "1 " <> fromString name <> ") "
  <> "(λ _, " <> genIType termf typef tl (AccT name (name <> "1") : acc) <> "))"
genIType termf typef ((Dep d s, name) : tl) acc =
  "P _ _ (P _ _ " <> (fromString $ val $ acc !! d) <> " (λ _, u " <> (fromString $ show s) <> ")) "
  <> "(λ " <> (fromString name) <> ", P _ _ "
     <> "(P _ _ (Pack' " <> (fromString $ orig $ acc !! d) <> " " <> (fromString $ val $ acc !! d) <> ") "
     <> "(λ p, H' (" <> fromString name <> "1 (projT1 p)) (" <> fromString name <> " (projT2 p)))) "
  <> "(λ _, " <> genIType termf typef tl (AccT name (name <> "1") : acc) <> "))"
genIType termf typef ((Term d t, name) : tl) acc =
  "P _ _ (P _ _ " <> (fromString $ val $ acc !! d) <> " " <> (fromString $ val $ acc !! t) <> ") "
  <> "(λ " <> (fromString name) <> ", P _ _ "
     <> "(P _ _ (Pack' " <> (fromString $ orig $ acc !! d) <> " " <> (fromString $ val $ acc !! d) <> ") "
     <> "(λ p, HEq' _ (" <> (fromString $ orig $ acc !! t) <> " (projT1 p)) "
        <> "(" <> (fromString $ val $ acc !! t) <> " (projT2 p)) "
        <> "(" <> fromString name <> "1 (projT1 p)) (" <> fromString name <> " (projT2 p)))) "
  <> "(λ _, " <> genIType termf typef tl (AccT name (name <> "1") : acc) <> "))"

genCong :: Builder -> ([String] -> String) -> ([String] -> String) -> [(Arg,String)] -> [AccT] -> Builder
genCong tabs termf typef [] acc = tabs <> "(heq_refl " <> (fromString $ typef $ fmap val acc) <> " " <> (fromString $ termf $ fmap val acc) <> ")"
genCong tabs termf typef ((Simple _, name) : tl) acc =
  let t = fromString name :: Builder in
  let hT = fromString ('h' : name) :: Builder in
    tabs <> "(λ _ " <> hT <> ", rewr (heq_to_eq " <> hT <> ")\n"
    <> tabs <> "  (λ " <> t <> ", " <> genIType termf typef tl (AccT name (name <> "1") : acc) <> ")\n"
    <> genCong (tabs <> "  ") termf typef tl (AccT (name <> "1") (name <> "1") : acc) <> ")"
genCong tabs termf typef ((Dep _ _, name) : tl) acc =
  let t = fromString name :: Builder in
  let hT = fromString ('h' : name) :: Builder in
    tabs <> "(λ " <> t <> " " <> hT <> ", rewr (packExtT " <> fromString name <> "1 " <> t <> " " <> hT <> ")\n"
    <> tabs <> "  (λ " <> t <> ", " <> genIType termf typef tl (AccT name (name <> "1") : acc) <> ")\n"
    <> genCong (tabs <> "  ") termf typef tl (AccT (name <> "1") (name <> "1") : acc) <> ")"
genCong tabs termf typef ((Term td tt, name) : tl) acc =
  let t = fromString name :: Builder in
  let hT = fromString ('h' : name) :: Builder in
    tabs <> "(λ(" <> t <> " : ε _ (P _ _ " <> (fromString $ val $ acc !! td) <> " " <> (fromString $ val $ acc !! tt) <> ")) " <> hT
       <> ", rewr (packExt " <> fromString name <> "1 " <> t <> " " <> hT <> ")\n"
    <> tabs <> "  (λ " <> t <> ", " <> genIType termf typef tl (AccT name (name <> "1") : acc) <> ")\n"
    <> genCong (tabs <> "  ") termf typef tl (AccT (name <> "1") (name <> "1") : acc) <> ")"


generators :: M.Map String ([(Arg,String)],[String] -> String,[String] -> String)
generators = M.fromList
           [ ("prod", ([(Simple (SVar "s"), "A"), (Dep 0 (SVar "s'"), "B")], \[b, a] -> "(P s s' " <> a <> " " <> b <> ")", \_ -> "(u (smax s s'))"))
           , ("lambda", ([(Simple (SVar "s"), "A"), (Dep 0 (SVar "s'"), "B"), (Term 1 0, "t")], \[t, _, _] -> t, \[_, b, a] -> "(P _ _ " <> a <> " " <> b <> ")"))
           ]

main :: IO ()
main = getArgs >>= \case
  [] -> putStrLn "Expected one argument"
  arg : _ -> (case M.lookup arg generators of
               Nothing -> putStrLn $ "Constructor " <> arg <> " not defined"
               Just (args,termf,typef) -> TIO.putStrLn $ toLazyText $ genCong "  " termf typef args [])
