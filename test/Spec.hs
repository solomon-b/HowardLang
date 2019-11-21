{-# LANGUAGE MultiParamTypeClasses #-}
import Control.Monad.Identity

import Test.Hspec
import Hedgehog (check)

import HowardLang.Parser
import HowardLang.Types
import HowardLang.Typechecker
import HowardLang.Interpreters


import Roundtrip

----------------------
--- Test Machinery ---
----------------------

class Yieldable m a where
  yields :: Eq a => a -> m a -> Bool

instance Yieldable Identity Term where
  yields s (Identity s') = s == s'

instance Yieldable (Either e) Term where
  yields s (Right s') = s == s'
  yields _ _ = False

instance Yieldable (Either e) Type where
  yields _ (Right _) = True
  yields _ _ = False

instance Yieldable Maybe Term where
  yields s (Just s') = s == s'
  yields _ _ = False

parseFailed :: Either ParseErr a -> Bool
parseFailed (Right _) = False
parseFailed _ = True

specParseYields :: String -> Term -> SpecWith ()
specParseYields s term =
  it ("parses " ++ show s ++ " as " ++ show term) $
    run pTerm s `shouldSatisfy` yields term

specParseFails :: String -> SpecWith ()
specParseFails s =
  it ("fails to parse " ++ show s) $
    run pTerm s `shouldSatisfy` parseFailed

specTypecheckYields :: Term -> Type -> SpecWith ()
specTypecheckYields t ty =
  it ("typechecks " ++ show t ++ " as " ++ show ty) $
    (runTypecheckM [] (typecheck t)) `shouldSatisfy` yields ty

specEvalYields :: Term -> Term -> SpecWith ()
specEvalYields t1 t2 =
  it ("evals " ++ show t1 ++ " as " ++ show t2) $
    Identity (multiStepEval [] t1) `shouldSatisfy` yields t2

checkParse :: SpecWith ()
checkParse = describe "Test Parser" $
  mapM_ (uncurry specParseYields) $ (\(str, ast, _) -> (str, ast)) <$> parseTests

checkTypes :: SpecWith ()
checkTypes = describe "Test Typechecker" $
  mapM_ (uncurry specTypecheckYields) $ (\(_, ast, _) -> (ast, NatT)) <$> parseTests

checkEval :: SpecWith ()
checkEval = describe "Test Eval" $
  mapM_ (uncurry specEvalYields) $ (\(_, ast, res) -> (ast, res)) <$> parseTests

main :: IO ()
main = do
  putStrLn "------------------"
  putStrLn "--- Unit Tests ---"
  putStrLn "------------------"

  hspec $ checkParse >> checkEval >> checkTypes

  --putStrLn "----------------------"
  --putStrLn "--- Property Tests ---"
  --putStrLn "----------------------"

  --void $ check bidirectional


---------------------
--- Parsing Tests ---
---------------------

parseTests :: [(String, Term, Term)]
parseTests =
  [ ( "True", Tru, Tru)
  , ( "False", Fls, Fls)
  , ( "Z", Z, Z)
  , ( "S Z", S Z, S Z)
  , ( "0", Z, Z)
  , ( "1", S Z, S Z)
  , ( "2", S (S Z), S (S Z))
  , ( "Unit", Unit, Unit)
  , ( "<0, True>", Pair Z Tru, Pair Z Tru)
  , ( "<0, <0, True>>", Pair Z (Pair Z Tru), Pair Z (Pair Z Tru))
  , ( "\\n:Nat.n", Abs "n" NatT (Var 0), Abs "n" NatT (Var 0))
  , ( "(\\n:Nat.n)", Abs "n" NatT (Var 0), Abs "n" NatT (Var 0))
  , ( "(\\m:Nat.\\n:Nat.n)", Abs "m" NatT $ Abs "n" NatT (Var 0), Abs "m" NatT $ Abs "n" NatT (Var 0))
  , ( "(\\m:Nat.\\n:Nat.m)", Abs "m" NatT $ Abs "n" NatT (Var 1), Abs "m" NatT $ Abs "n" NatT (Var 1))
  , ( "(\\p:Bool.\\m:Nat.\\n:Nat.p)"
    , Abs "p" BoolT $ Abs "m" NatT $ Abs "n" NatT (Var 2)
    , Abs "p" BoolT $ Abs "m" NatT $ Abs "n" NatT (Var 2))
  , ( "(\\f:Nat->Bool.\\n:Nat.f n)"
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (App (Var 1) (Var 0))
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (App (Var 1) (Var 0)))
  , ( "(\\n:Nat.case n of Z => True | (S m) => False)"
    , Abs "n" NatT (Case (Var 0) Tru "m" Fls)
    , Abs "n" NatT (Case (Var 0) Tru "m" Fls))
  , ( "(\\n:Nat.case n of Z => 0 | (S m) => n)"
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 1))
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 1)))
  , ( "(\\n:Nat.case n of Z => 0 | (S m) => m)"
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 0))
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 0)))
  , ( "(True as Bool)", As Tru BoolT, Tru)
  , ( "(Z as Nat)", As Z NatT, Z)
  , ( "(2 as Nat)", As (S $ S Z) NatT, S (S Z))
  , ( "\\n:Nat.(n as Nat)", Abs "n" NatT (As (Var 0) NatT), Abs "n" NatT (As (Var 0) NatT))
  , ( "(\\f:Nat->Bool.\\n:Nat.((f n) as Bool))"
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (As (App (Var 1) (Var 0)) BoolT)
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (As (App (Var 1) (Var 0)) BoolT)
    )
  , ( "(\\f:Nat->Bool.\\n:Nat.((f n) as Bool)) (\\g:Nat.True)"
    , App (Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (As (App (Var 1) (Var 0)) BoolT)) (Abs "g" NatT Tru)
    , Abs "n" NatT (As (App (Abs "g" NatT Tru) (Var 0)) BoolT)
    )
  , ( "(\\f:Nat->Bool.\\n:Nat.((f n) as Bool)) (\\g:Nat.True) Z"
    , App (App (Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (As (App (Var 1) (Var 0)) BoolT)) (Abs "g" NatT Tru)) Z
    , Tru
    )
  , ( "\\n:Nat.let f = (\\m:Nat.S m) in n"
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (Var 1)
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (Var 1)
    )
  , ( "\\n:Nat.let f = (\\m:Nat.S m) in (n as Nat)"
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (As (Var 1) NatT)
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (As (Var 1) NatT)
    )
  , ( "\\n:Nat.let f = (\\m:Nat.S m) in f n"
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (App (Var 0) (Var 1))
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (App (Var 0) (Var 1))
    )
  , ( "(\\n:Nat.let f = (\\m:Nat.S m) in f n) Z"
    , App (Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (App (Var 0) (Var 1))) Z
    , S Z
    )
  , ( "(\\n:Nat.let x = case n of Z => True | (S m) => False in x)"
    , Abs "n" NatT $ Let "x" (Case (Var 0) Tru "m" Fls) (Var 0)
    , Abs "n" NatT $ Let "x" (Case (Var 0) Tru "m" Fls) (Var 0))
  , ( "(\\n:Nat.let x = case n of Z => True | (S m) => False in x) Z"
    , App (Abs "n" NatT $ Let "x" (Case (Var 0) Tru "m" Fls) (Var 0)) Z
    , Tru
    )
  , ( "(\\n:Nat.let x = case n of Z => (\\q:Nat.n) | (S m) => (\\z:Nat.m) in x)"
    , Abs "n" NatT $ Let "x" (Case (Var 0) (Abs "q" NatT (Var 1)) "m" (Abs "z" NatT (Var 1))) (Var 0)
    , Abs "n" NatT $ Let "x" (Case (Var 0) (Abs "q" NatT (Var 1)) "m" (Abs "z" NatT (Var 1))) (Var 0)
    )
  , ( "(\\f:Nat->Nat.\\n:Nat.let x = case n of Z => (\\z:Nat.\\q:Nat.n) | (S m) => (\\h:Nat.\\z:Nat.m) in f (x Z Z)) (\\x:Nat.x) (S S Z)"
    , (App
        (App
          (Abs "f" (FuncT NatT NatT) (Abs "n" NatT (Let "x" (Case (Var 0) (Abs "z" NatT (Abs "q" NatT (Var 2))) "m" (Abs "h" NatT (Abs "z" NatT (Var 2)))) (App (Var 2) (App (App (Var 0) Z) Z)))))
          (Abs "x" NatT (Var 0)))
        (S (S Z)))
    , (S Z)
    )
  , ( "fst <True, False>", Fst $ Pair Tru Fls, Tru)
  , ( "snd <True, False>", Snd $ Pair Tru Fls, Fls)
  , ( "\\p:Bool.if: p then: 1 else: 0"
    , Abs "p" BoolT (If (Var 0) (S Z) Z)
    , Abs "p" BoolT (If (Var 0) (S Z) Z)
    )
  , ( "\\p:Bool.if: p then: (\\x:Nat.p) else: (\\x:Nat.True)"
    , Abs "p" BoolT (If (Var 0) (Abs "x" NatT (Var 1)) (Abs "x" NatT Tru))
    , Abs "p" BoolT (If (Var 0) (Abs "x" NatT (Var 1)) (Abs "x" NatT Tru)))
  , ("(\\f:Nat->Bool.\\n:Nat.case n of Z => f n | (S m) => f n) (\\m:Nat.True)"
    , App
       (Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT $ Case (Var 0) (App (Var 1) (Var 0)) "m" (App (Var 2) (Var 1))) (Abs "m" NatT Tru)
    , Abs "n" NatT $ Case (Var 0) (App (Abs "m" NatT Tru) (Var 0)) "m" (App (Abs "m" NatT Tru) (Var 1))) 
  , ( "(\\f:Nat->Nat.\\n:Nat.let p = (case (f n) of Z => Z | (S m) => m) in p) (\\n:Nat.S n) 1"
    , App
       (App
        (Abs "f" (FuncT NatT NatT)
         (Abs "n" NatT
          (Let "p"
           (Case (App (Var 1) (Var 0)) Z "m" (Var 0))
           (Var 0))))
        (Abs "n" NatT (S (Var 0))))
       (S Z)
    , (S Z)
    )
  , ( "(\\z:Bool.let f = (\\x:Bool.if: x then: 1 else: 0) in f z) "
    , (Abs "z" BoolT
        (Let "f"
         (Abs "x" BoolT
          (If (Var 0) (S Z) Z)) (App (Var 0) (Var 1))))
    , (Abs "z" BoolT
        (Let "f"
         (Abs "x" BoolT
          (If (Var 0) (S Z) Z)) (App (Var 0) (Var 1))))
    )
  , ( "(\\z:Bool.let f = (\\x:Bool.if: x then: 1 else: 0) in f z) False"
    , (App
       (Abs "z" BoolT
        (Let "f"
         (Abs "x" BoolT
          (If (Var 0) (S Z) Z)) (App (Var 0) (Var 1)))) Fls)
    , Z
    )
  ]

{-



(\ie:Nat->Bool.\x:Nat.
  let iszero = (\n:Nat.case n of Z => True | (S m) => False)
  in (let pred = (\n:Nat.case n of Z => Z | (S m) => m)
  in (if: iszero x then: True else: (if: iszero (pred x) then: False else: (ie (pred (pred x)))))))

(\ie:Nat->Bool.\x:Nat. let iszero = (\n:Nat.case n of Z => True | (S m) => False) in (let pred = (\n:Nat.case n of Z => Z | (S m) => m) in (if: iszero x then: True else: (if: iszero (pred x) then: False else: (ie (pred (pred x)))))))
-}
