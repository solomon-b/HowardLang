{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
import Control.Monad.Identity

import Text.RawString.QQ
import Test.Hspec
-- import Hedgehog (check)

import HowardLang.Parser
import HowardLang.PrettyPrinter
import HowardLang.Types
import HowardLang.Typechecker
import HowardLang.AscribeTree
import HowardLang.Interpreters


-- import Roundtrip

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
    run pMain s `shouldSatisfy` yields term

specParseFails :: String -> SpecWith ()
specParseFails s =
  it ("fails to parse " ++ show s) $
    run pMain s `shouldSatisfy` parseFailed

specTypecheckYields :: Term -> Type -> SpecWith ()
specTypecheckYields t ty =
  it ("typechecks " ++ show t ++ " as " ++ show ty) $
    runTypecheckM [] (typecheck . ascribeRolls $ t) `shouldSatisfy` yields ty

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
  -- Base Types
  [ ( "True", Tru, Tru)
  , ( "False", Fls, Fls)
  , ( "Z", Z, Z)
  , ( "S Z", S Z, S Z)
  , ( "0", Z, Z)
  , ( "1", S Z, S Z)
  , ( "2", S (S Z), S (S Z))
  , ( "Unit", Unit, Unit)
  ] ++
  -- 'Container' Types
  [ ( "<0, True>", Pair Z Tru, Pair Z Tru)
  , ( "<0, <0, True>>", Pair Z (Pair Z Tru), Pair Z (Pair Z Tru))
  , ( "fst <0, <0, True>>", Fst (Pair Z (Pair Z Tru)), Z)
  , ( "snd <0, <0, True>>", Snd (Pair Z (Pair Z Tru)), Pair Z Tru)
  , ( "(1, True, Unit)", Tuple [("0", S Z),("1", Tru),("2", Unit)], Tuple [("0", S Z),("1", Tru),("2", Unit)])
  , ( "{foo=1, bar=True}", Record [("foo", S Z),("bar", Tru)], Record [("foo", S Z),("bar", Tru)])
  , ( "inl Unit : Sum Unit Bool", InL Unit (SumT UnitT BoolT), InL Unit (SumT UnitT BoolT))
  , ( "inr True : Sum Unit Bool", InR Tru (SumT UnitT BoolT), InR Tru (SumT UnitT BoolT))
  , ( "tag Just 1 as Nothing | Just Nat"
    , As (Tag "Just" (S Z)) (VariantT [("Nothing", UnitT), ("Just", NatT)])
    , Tag "Just" (S Z)
    )
  , ( "tag Nothing as Nothing | Just Nat"
    , As (Tag "Nothing" Unit) (VariantT [("Nothing", UnitT), ("Just", NatT)])
    , Tag "Nothing" Unit)
  ] ++
  -- Accesors
  [ ( "fst <0, <0, True>>", Fst (Pair Z (Pair Z Tru)), Z)
  , ( "snd <0, <0, True>>", Snd (Pair Z (Pair Z Tru)), Pair Z Tru)
  , ( "get (1, True, Unit).0", Get (Tuple [("0", S Z),("1", Tru),("2", Unit)]) "0", S Z)
  , ( "get (1, True, Unit).2", Get (Tuple [("0", S Z),("1", Tru),("2", Unit)]) "2", Unit)
  , ( "get {foo=Unit, bar=True}.foo", Get (Record [("foo", Unit), ("bar", Tru)]) "foo", Unit)
  , ( "get {foo=Unit, bar=True}.bar", Get (Record [("foo", Unit), ("bar", Tru)]) "bar", Tru)
  ] ++
  -- Abstraction
  [ ( [r| \n:Nat.n |], Abs "n" NatT (Var 0), Abs "n" NatT (Var 0))
  , ( [r| (\n:Nat.n) |], Abs "n" NatT (Var 0), Abs "n" NatT (Var 0))
  , ( [r| (\m:Nat.\n:Nat.n) |], Abs "m" NatT $ Abs "n" NatT (Var 0), Abs "m" NatT $ Abs "n" NatT (Var 0))
  , ( [r| (\m:Nat.\n:Nat.m) |], Abs "m" NatT $ Abs "n" NatT (Var 1), Abs "m" NatT $ Abs "n" NatT (Var 1))
  , ( [r|(\p:Bool.\m:Nat.\n:Nat.p)|]
    , Abs "p" BoolT $ Abs "m" NatT $ Abs "n" NatT (Var 2)
    , Abs "p" BoolT $ Abs "m" NatT $ Abs "n" NatT (Var 2))
  , ( [r|(\p:Bool. (\q:Bool.q) p)|]
    , Abs "p" BoolT (App (Abs "q" BoolT (Var 0)) (Var 0))
    , Abs "p" BoolT (App (Abs "q" BoolT (Var 0)) (Var 0)))
  , ( [r|(\p:Bool. (\q:Bool.q) p) True|]
    , App (Abs "p" BoolT (App (Abs "q" BoolT (Var 0)) (Var 0))) Tru
    , Tru)
  , ( [r|(\f:Nat->Bool.\n:Nat.f n)|]
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (App (Var 1) (Var 0))
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (App (Var 1) (Var 0)))
  , ( [r|(\n:Nat.case n of Z => True | (S m) => False)|]
    , Abs "n" NatT (Case (Var 0) Tru "m" Fls)
    , Abs "n" NatT (Case (Var 0) Tru "m" Fls))
  , ( [r|(\n:Nat.case n of Z => 0 | (S m) => n)|]
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 1))
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 1)))
  , ( [r|(\n:Nat.case n of Z => 0 | (S m) => m)|]
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 0))
    , Abs "n" NatT (Case (Var 0) Z "m" (Var 0)))
  ] ++
  -- Let
  [ ( "let x = 0 in x", Let "x" Z (Var 0), Z)
  , ( "let f = (\\x:Nat.x) in f", Let "f" (Abs "x" NatT (Var 0)) (Var 0), Abs "x" NatT (Var 0))
  , ( "let f = (\\x:Nat.x) in f Z", Let "f" (Abs "x" NatT (Var 0)) (App (Var 0) Z), Z)
  , ( "let f (x : Nat) = x in f", Let "f" (Abs "x" NatT (Var 0)) (Var 0), Abs "x" NatT (Var 0))
  , ( "let f (x : Nat) = x in f Z", Let "f" (Abs "x" NatT (Var 0)) (App (Var 0) Z), Z)
  , ( "let f (x : Nat) (p : Bool) = x in f Z"
    , Let "f" (Abs "x" NatT (Abs "p" BoolT (Var 1))) (App (Var 0) Z), Abs "p" BoolT Z)
  ] ++
  -- Ascription
  [ ( "(True as Bool)", As Tru BoolT, Tru)
  , ( "(Z as Nat)", As Z NatT, Z)
  , ( "(2 as Nat)", As (S $ S Z) NatT, S (S Z))
  , ( "\\n:Nat.(n as Nat)", Abs "n" NatT (As (Var 0) NatT), Abs "n" NatT (Var 0))
  , ( "(\\f:Nat->Bool.\\n:Nat.((f n) as Bool))"
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (As (App (Var 1) (Var 0)) BoolT)
    , Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (App (Var 1) (Var 0))
    )
  , ( "(\\f:Nat->Bool.\\n:Nat.((f n) as Bool)) (\\g:Nat.True)"
    , App (Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (As (App (Var 1) (Var 0)) BoolT)) (Abs "g" NatT Tru)
    , Abs "n" NatT (App (Abs "g" NatT Tru) (Var 0))
    )
  , ( "(\\f:Nat->Bool.\\n:Nat.((f n) as Bool)) (\\g:Nat.True) Z"
    , App (App (Abs "f" (FuncT NatT BoolT) $ Abs "n" NatT (As (App (Var 1) (Var 0)) BoolT)) (Abs "g" NatT Tru)) Z
    , Tru
    )
  ] ++
  --  If Statements
  [ ( "if: True then: 1 else: 0", If Tru (S Z) Z, S Z)
  , ( "if: False then: 1 else: 0", If Fls (S Z) Z, Z)
  , ( "if: ((\\p:Bool.p) True) then: 1 else: 0", If (App (Abs "p" BoolT (Var 0)) Tru) (S Z) Z, S Z)
  , ( "\\p:Bool.if: p then: 1 else: 0"
    , Abs "p" BoolT (If (Var 0) (S Z) Z)
    , Abs "p" BoolT (If (Var 0) (S Z) Z))
  , ( "(\\p:Bool.if: p then: 1 else: 0) True"
    , App (Abs "p" BoolT (If (Var 0) (S Z) Z)) Tru
    , S Z)
  ] ++
  -- Nat Case
  [ ( "case Z of Z => True | (S m) => False", Case Z Tru "m" Fls, Tru)
  , ( "case 1 of Z => True | (S m) => False", Case (S Z) Tru "m" Fls, Fls)
  , ( "case 2 of Z => Z | (S m) => m", Case (S $ S Z) Z "m" (Var 0), S Z)
  ] ++
  -- Sum Case
  [ ( "sumCase (inr True : Sum Unit Bool) of inl l => False | inr r => True"
    , SumCase (InR Tru (SumT UnitT BoolT)) Fls "l" Tru "r"
    , Tru)
  , ( "sumCase (inl Unit : Sum Unit Bool) of inl l => False | inr r => True"
    , SumCase (InL Unit (SumT UnitT BoolT)) Fls "l" Tru "r"
    , Fls)
  ] ++
  -- Variant Case
  [ ( "variantCase (tag Nothing as Nothing | Just Nat) of Nothing => False | Just=x => True"
    , VariantCase (As (Tag "Nothing" Unit) (VariantT [("Nothing", UnitT),("Just", NatT)]))
      [("Nothing", Nothing, Fls), ("Just", Just "x", Tru)]
    , Fls)
  , ( "variantCase (tag Just Z as Nothing | Just Nat) of Nothing => False | Just=x => True"
    , VariantCase (As (Tag "Just" Z) (VariantT [("Nothing", UnitT),("Just", NatT)]))
      [("Nothing", Nothing, Fls), ("Just", Just "x", Tru)]
    , Tru)
  , ( "variantCase (tag Just 1 as Nothing | Just Nat) of Nothing => Z | Just=x => x"
    , VariantCase (As (Tag "Just" (S Z)) (VariantT [("Nothing", UnitT),("Just", NatT)]))
      [("Nothing", Nothing, Z), ("Just", Just "x", Var 0)]
    , S Z)
  ] ++
  -- Recursive Functions
  [ ( [r|let isZero (n : Nat) = case n of Z => True | (S m) => False in let pred (n : Nat) = case n of Z => Z | (S m) => m in letrec isEven(rec : Nat -> Bool) (n : Nat) = if: isZero n then: True else: if: isZero (pred n) then: False else: rec (pred (pred n)) in isEven 4 |]
      , Let "isZero" (Abs "n" NatT (Case (Var 0) Tru "m" Fls)) (Let "pred" (Abs "n" NatT (Case (Var 0) Z "m" (Var 0))) (Let "isEven" (Fix (Abs "rec" (FuncT NatT BoolT) (Abs "n" NatT (If (App (Var 3) (Var 0)) Tru (If (App (Var 3) (App (Var 2) (Var 0))) Fls (App (Var 1) (App (Var 2) (App (Var 2) (Var 0))))))))) (App (Var 0) (S (S (S (S Z)))))))
      , Tru)
  , ( [r|(fix (\rec:Nat->Nat->Nat.\x:Nat.\y:Nat.case x of Z => y | (S z) => rec z (S y))) 2 2|]
    , App (App (Fix (Abs "rec" (FuncT NatT (FuncT NatT NatT)) (Abs "x" NatT (Abs "y" NatT (Case (Var 1) (Var 0) "z" (App (App (Var 3) (Var 0)) (S (Var 1)))))))) (S (S Z))) (S (S Z))
    , S (S (S (S Z)))
    )
  ] ++
  -- Recursive Types
  [ ([r|(tag Cons (3, tag Cons (2, tag Cons (1, tag Nil))) as mu.NatList: Nil | Cons (Nat, NatList))|]
    , Roll (FixT "NatList" (VariantT [("Nil",UnitT),("Cons",TupleT [NatT,VarT 0])])) (Tag "Cons" (Tuple [("0",S (S (S Z))),("1",Tag "Cons" (Tuple [("0",S (S Z)),("1",Tag "Cons" (Tuple [("0",S Z),("1",Tag "Nil" Unit)]))]))]))
    , Roll (FixT "NatList" (VariantT [("Nil",UnitT),("Cons",TupleT [NatT,VarT 0])])) (Tag "Cons" (Tuple [("0",S (S (S Z))),("1",Tag "Cons" (Tuple [("0",S (S Z)),("1",Tag "Cons" (Tuple [("0",S Z),("1",Tag "Nil" Unit)]))]))])))
  ] ++
  -- Mixed Expressions
  [ ( "\\n:Nat.let f = (\\m:Nat.S m) in n"
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (Var 1)
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (Var 1)
    )
  , ( "\\n:Nat.let f = (\\m:Nat.S m) in (n as Nat)"
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (As (Var 1) NatT)
    , Abs "n" NatT $ Let "f" (Abs "m" NatT (S (Var 0))) (Var 1)
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
