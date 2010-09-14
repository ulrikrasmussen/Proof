module Proof.Language(
   Phi(..)
 , Sequent(..)
 , showPhi
 , asciiFormat
 , latexFormat
 , Premise) where

data Phi = L String
         | Phi :&: Phi
         | Phi :|: Phi
         | Phi :-> Phi
         | Not Phi
         | Bot
 deriving (Eq, Ord)

infixr 0 :->
infixl 1 :|:
infixl 2 :&:

type Premise = Phi

data Sequent = [Premise] :- Phi
 deriving (Eq,Show)

instance Show Phi where
  show phi = showPhi asciiFormat phi

data PrintFormat = PF {
  pfAnd :: String,
  pfOr  :: String,
  pfImp :: String,
  pfNot :: String,
  pfBot :: String
}

asciiFormat = PF {
    pfAnd = " & "
  , pfOr  = " | "
  , pfImp = " -> "
  , pfNot = "not "
  , pfBot = "_|_"
}

latexFormat = PF {
    pfAnd = "{\\land}"
  , pfOr  = "{\\lor}"
  , pfImp = "{\\rightarrow}"
  , pfNot = "{\\lnot}"
  , pfBot = "{\\bot}"
}

parens :: String -> Int -> Int -> String
parens s opPrec prec = if prec > opPrec then "(" ++ s ++ ")" else s

showPhi :: PrintFormat -> Phi -> String
showPhi pf phi = showPhi' pf phi 0
  where
    showPhi' :: PrintFormat -> Phi -> Int -> String
    showPhi' pf (L l) _ = l
    showPhi' pf Bot _ = pfBot pf
    showPhi' pf (p1 :&: p2) prec =
      let s = showPhi' pf p1 2 ++ pfAnd pf ++ showPhi' pf p2 2
       in parens s 2 prec
    showPhi' pf (p1 :|: p2) prec =
      let s = showPhi' pf p1 1 ++ pfOr pf ++ showPhi' pf p2 1
       in parens s 1 prec
    showPhi' pf (p1@(_ :-> _) :-> p2) prec =
      let s = "(" ++ showPhi' pf p1 0 ++ ")" ++ pfImp pf ++ showPhi' pf p2 0
       in parens s 0 prec
    showPhi' pf (p1 :-> p2) prec =
      let s = showPhi' pf p1 0 ++ pfImp pf ++ showPhi' pf p2 0
       in parens s 0 prec
    showPhi' pf (Not p) prec =
      pfNot pf ++ parens (showPhi' pf p 3) 3 prec
