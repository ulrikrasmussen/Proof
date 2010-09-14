module Proof.Language(
   Phi(..)
 , Sequent(..)
 , showPhi
 , asciiFormat
 , latexFormat
 , Premise
 , implFree
 , nnf
 , cnf) where

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

implFree :: Phi -> Phi
implFree (a :-> b) = Not (implFree a) :|: implFree b
implFree (a :|: b) = implFree a :|: implFree b
implFree (a :&: b) = implFree a :&: implFree b
implFree (Not p) = Not $ implFree p
implFree (L s) = L s
implFree Bot = Bot

nnf :: Phi -> Phi
nnf (Not (Not a)) = nnf a
nnf (Not (a :&: b)) = nnf (Not a) :|: nnf (Not b)
nnf (Not (a :|: b)) = nnf (Not a) :&: nnf (Not b)
nnf (a :&: b) = nnf a :&: nnf b
nnf (a :|: b) = nnf a :|: nnf b
nnf (L s) = L s
nnf (Not (L s)) = Not (L s)

distr :: Phi -> Phi -> Phi
distr (n11 :&: n12) n2 = distr n11 n2 :&: distr n12 n2
distr n1 (n21 :&: n22) = distr n1 n21 :&: distr n1 n22
distr n1 n2 = n1 :|: n2

cnf (p1 :&: p2) = cnf p1 :&: cnf p2
cnf (p1 :|: p2) = distr (cnf p1) (cnf p2)
cnf x = x
