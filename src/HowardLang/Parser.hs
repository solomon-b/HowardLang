module HowardLang.Parser
  ( module HowardLang.Parser.Combinators
  , module HowardLang.Parser.Token
  , module HowardLang.Parser.Expression
  ) where

import HowardLang.Parser.Combinators
import HowardLang.Parser.Token
import HowardLang.Parser.Expression

-----------------------
----- BNF Grammer -----
-----------------------

{-
SHINY NEW TYPE PARSER

TYPE = "(" TYPE ")" | START END
START = UNIT | NAT | BOOL | SUM | VARIANT | TUPLE | RECORD | FIXT
END = "X" TYPE | "->" TYPE | EPSILON

FIXT = "mu." VAR TYPE
RECORD = "{" TYPE { , TYPE } "}"
TUPLE = "( TYPE { , TYPE } ")"
VARIANT = VAR [TYPE] { | VAR [TYPE] }
SUM = "SUM" TYPE TYPE
UNIT = "Unit" | "()"
NAT = "Nat"
BOOL = "Bool"
-}

{-
CURRENT TERM PARSER  TODO: UPDATE THIS

ALPHA = "A".."Z" | "a".."z";
DIGIT = "0".."9";
INTEGER = DIGIT {DIGIT};

APP = TERM TERM;

ABS = ("\\" | "λ") VAR ":" TYPE "." TERM;
CASE = "case" TERM "of" "Z" "=>" TERM "|" "(S" VAR ")" "=>" TERM;
IF = "if:" TERM "then:" TERM "else:" TERM;
PAIR = "<" TERM "," TERM ">";
FST = "fst" TERM;
SND = "snd" TERM;
TUPLE = "(" TERM { "," TERM } ")";
PROJ = "get" TERM "[" VAR "]";
RECORD = "{" VAR "=" TERM { "," VAR "=" TERM } "}";
GROUP = "(" TERM ")";
INR = "inr" TERM TYPE;
INL = "inl" TERM TYPE;
SUMCASE = "sumCase" TERM "of" "(" "inl" VAR ")" "=>" TERM "|" "(" "inr" VAR ")" "=>" TERM;
TAG = "tag" VAR TERM "as" TYPE;
VARIANTCASE = "variantCase" TERM "of" VAR VAR "=>" TERM { "|" VAR VAR "=>" TERM };
FIX = fix TERM
LET = "let" VAR {"(" VAR ":" "TYPE" ")"} "=" TERM "in" TERM
LETREC = "letrec" VAR "=" TERM "in" TERM

TERM = GROUP | VAR | S | Z | BOOL | APP | ABS | CASE | IF | PAIR | FST | SND | TUPLE | PROJ | RECORD | INR | INL | SUMCASE | FIX | LET | LETREC;

TERM = 
START = VAR | UNIT | BOOL | Z | S 
END = TERM | 

VAR = ALPHA {ALPHA | INTEGER};
UNIT = "Unit" | "()";
BOOL = "True" | "False";
Z = "Z" | "0";
S = "S" TERM;




Example Expressions:

(\x:Nat.x) === Abs "x" NatT (Var 0)

Example Type Signatures:
Product Type:
(Nat, Bool) === (NatT, BoolT)

Variant Type:
(Left Bool | Right Nat) === VarantT [("Left", BoolT), ("Right, NatT")]

Enumerated Type:
(Nothing | Just Nat) === VariantT [("Nothing", UnitT), ("Just", NatT)]
(Red | Blue | Green) === VariantT [("Red", UnitT), ("Blue", UnitT), ("Green", UnitT)]

Recursive Type:
mu. List: (Nil | Cons a List a)

-}
