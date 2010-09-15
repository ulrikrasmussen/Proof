{-# LANGUAGE GeneralizedNewtypeDeriving #-}

----------------------------------------------------------------------
-- |
-- Module   : Proof.Monad
--
-- Monad for checking proofs in propositional logic.
----------------------------------------------------------------------

module Proof.Monad(
    Proof, LatexProof,
    Fact, getFact,
    CondFact, getCond,
    MonadProof,
    derivedRule,
    assume,
    prem,
    and_el, and_er, and_i,
    or_e, or_il, or_ir,
    imp_i, imp_e,
    not_e, not_i,
    nn_e,
    bot_e,
    check, checkTauto, checkLatex,
    (.::)
) where

import Data.List
import qualified Data.Map as M

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Trans
import Control.Applicative

import Proof.Language

data Context = Context { premises :: [Premise] }

newtype Fact = Fact { getFact :: Phi }
 deriving (Show, Eq, Ord)

data CondFact = CondFact { getCond :: Phi, getCondFact :: Phi }
 deriving (Show, Eq, Ord)

newtype Proof a = P { runProof :: ReaderT Context (Either String) a}
 deriving (Monad, MonadError String, MonadReader Context, Functor)

data LatexState = LS {
  outLines        :: [String]
 ,factLabels      :: M.Map Fact String
 ,condFactLabels  :: M.Map CondFact (String, String)
 ,freshNames      :: [String]
}

newtype LatexProof a = LP { runLatex :: StateT LatexState Proof a }
 deriving (Monad, Functor, MonadState LatexState)

writeLine :: String -> LatexProof ()
writeLine l = modify (\s -> s { outLines = l:outLines s })

writeLine' = writeLine'' True

writeLine'' :: Bool            -- ^ Render with line break?
           -> Proof Fact       -- ^ Proof
           -> String           -- ^ Justification
           -> [Fact]           -- ^ Dependencies
           -> [CondFact]       -- ^ Conditional dependencies
           -> LatexProof Fact
writeLine'' nl proof name deps cdeps = do
  res <- LP . lift $ proof
  lbl <- getFresh
  frefs <- map (\l -> "\\ref{" ++ l ++ "}")
        <$> mapM getFactLabel deps
  crefs <- map (\(s,e) -> "\\ref{" ++ s ++ "} - \\ref{" ++ e ++ "}")
        <$> mapM getCondFactLabel cdeps
  let refs = concat . intersperse "," $ crefs ++ frefs
  let premise = name ++ if null deps && null cdeps then "" else "(" ++ refs ++ ")"
  writeLine $ (if nl then "\\\\ " else "") ++ "\\\"" ++ lbl ++ "\" \\: "
              ++ showPhi latexFormat (getFact res)
              ++ " \\= " ++ premise
  putFactLabel res lbl
  return res

getFresh :: LatexProof String
getFresh = do
  fresh <- gets freshNames
  modify $ \s -> s { freshNames = tail fresh }
  return $ head fresh

putFactLabel :: Fact -> String -> LatexProof ()
putFactLabel f l = modify $ \s -> s { factLabels = M.insert f l (factLabels s) }

putCondFactLabel :: CondFact -> String -> String -> LatexProof ()
putCondFactLabel f st en =
  modify $ \s -> s { condFactLabels = M.insert f (st,en) (condFactLabels s) }

getFactLabel :: Fact -> LatexProof String
getFactLabel f = (M.! f) <$> gets factLabels

getCondFactLabel :: CondFact -> LatexProof (String, String)
getCondFactLabel f = (M.! f) <$> gets condFactLabels

class (Monad m) => MonadProof m where
  derivedRule :: String -> [Fact] -> [CondFact] -> m Fact -> m Fact
  failProof :: String -> m a
  assume :: Phi -> (Fact -> m Fact) -> m CondFact
  prem   :: Phi -> m Fact
  and_el :: Fact -> m Fact
  and_er :: Fact -> m Fact
  and_i  :: Fact -> Fact -> m Fact
  imp_i  :: CondFact -> m Fact
  imp_e  :: Fact -> Fact -> m Fact
  bot_e  :: Fact -> Phi -> m Fact
  not_e  :: Fact -> Fact -> m Fact
  nn_e   :: Fact -> m Fact
  not_i  :: CondFact -> m Fact
  or_e   :: Fact -> CondFact -> CondFact -> m Fact
  or_il  :: Fact -> Phi -> m Fact
  or_ir  :: Phi -> Fact -> m Fact


-- |Checks if a proof proves a given sequent.
check :: Sequent -> Proof Fact -> Either String ()
check (prems :- phi) proof =
  case runReaderT (runProof proof) (Context prems) of
    Left err -> Left err
    Right (Fact phi') ->
      if (phi == phi')
         then Right ()
         else Left $ "check: invalid conclusion: reached '"
                     ++ show phi' ++ "', expected '"
                     ++ show phi ++ "'"

-- |Checks a proof of a tautology.
checkTauto :: Proof Fact -> Either String Sequent
checkTauto proof =
  case runReaderT (runProof proof) (Context []) of
    Left err -> Left err
    Right (Fact phi) -> Right ([] :- phi)

checkLatex :: Sequent -> LatexProof Fact -> Either String String
checkLatex (prems :- phi) proof =
  case (runReaderT (runProof (runStateT (runLatex proof) initState)) (Context prems)) of
    Left err -> Left err
    Right (Fact phi', s) ->
      if phi == phi'
         then Right . wrap . concat . intersperse "\n" . reverse $ outLines s
         else Left $ "checkLatex: invalid conclusion: reached '"
                     ++ show phi' ++ "', expected '"
                     ++ show phi ++ "'"
   where
     wrap s = "\\begin{proofbox}\n" ++ s ++ "\n\\end{proofbox}\n"
     initState = LS [] (M.fromList []) (M.fromList []) freshNames
     freshNames = ["l" ++ show n | n <- [1..]]

-- |Proof signature. (For debugging proofs).
(.::) :: (MonadProof m) => m Fact -> Phi -> m Fact
p .:: f' = do
  (Fact f) <- p
  when (f /= f') . failProof $
    "Conclusion mismatch: Got '" ++ show f ++ "' expected '" ++ show f' ++ "'"
  return (Fact f)

infixl 0 .::


instance MonadProof Proof where
  derivedRule _ _ _ m = m

  failProof = throwError

  assume p m = do f <- local (\ctx -> ctx { premises = p:premises ctx} ) (m (Fact p))
                  return $ CondFact p (getFact f)

  prem p = do prems <- premises <$> ask
              if p `elem` prems then return (Fact p)
                                else throwError $ "prem: Not a premise: " ++ show p

  and_el (Fact (a :&: b)) = return $ Fact a
  and_el f = throwError $ "and_el: Invalid premise: " ++ show f

  and_er (Fact (a :&: b)) = return $ Fact b
  and_er f = throwError $ "and_er: Invalid premise: " ++ show f

  and_i (Fact a) (Fact b) = return . Fact $ a :&: b

  imp_i (CondFact p f) = return . Fact $ p :-> f

  imp_e (Fact phi) (Fact (phi' :-> psi)) =
    if phi == phi'
       then return $ Fact psi
       else throwError $ "imp_e: Premises do not match: '"
                         ++ show phi ++ "' and '" ++ show phi' ++ "'"
  imp_e _ (Fact f) = throwError $ "imp_e: Premise not an implication: " ++ show f

  bot_e (Fact Bot) p = return . Fact $ p
  bot_e f p = throwError $ "bot_e: Invalid premise: " ++ show f

  not_e (Fact a) (Fact (Not a')) =
    if a == a'
       then return $ Fact Bot
       else throwError $ "not_e: Subformulas does not match: '"
                          ++ show a ++ "' and '" ++ show a' ++ "'"

  nn_e (Fact (Not (Not p))) = return $ Fact p
  nn_e f = throwError $ "nn_e: Invalid premise: " ++ show f

  not_i (CondFact p Bot) = return . Fact $ Not p
  not_i (CondFact p f) = throwError $ "not_i: Conclusion in conditional proof is not bottom: "
                                       ++ show f

  or_e (Fact (a :|: b)) (CondFact a' x1) (CondFact b' x2) = do
    when (a /= a') . throwError $
      "or_e: Assumption in first conditional "
      ++ "fact does not match left subformula: "
      ++ "'" ++ show a ++ "' and '" ++ show a' ++ "'"
    when (b /= b') . throwError $
      "or_e: Assumption in second conditional "
      ++ "fact does not match right subformula: "
      ++ "'" ++ show b ++ "' and '" ++ show b' ++ "'"
    when (x1 /= x2) . throwError $
      "or_e: Conclusions in conditional subproofs does not match: "
      ++ "'" ++ show x1 ++ "' and '" ++ show x2 ++ "'"
    return . Fact $ x1

  or_il (Fact a) b = return . Fact $ a :|: b

  or_ir a (Fact b) = return . Fact $ a :|: b


instance MonadProof LatexProof where
  derivedRule name deps cdeps proof = do
    s <- get
    (fact, s') <- LP . lift $ runStateT (runLatex proof) s
    put $ s' {outLines = outLines s} -- Suppress output from proof
    writeLine' (return fact) name deps cdeps

  failProof = LP . lift . throwError

  assume p f = do
    lStart <- getFresh
    writeLine $ "\\[" ++ "\\label{" ++ lStart ++ "}"
    writeLine'' False (return (Fact p)) "\\ass" [] []
    s <- get
    let m = runStateT (runLatex (f (Fact p))) s
    (Fact res, s') <- LP . lift $ local (\ctx -> ctx { premises = p:premises ctx }) m
    put s'
    lEnd <- getFresh
    writeLine $ "\\label{" ++ lEnd ++ "}\\]"
    let cFact = CondFact p res
    putCondFactLabel cFact lStart lEnd
    return cFact

  prem p = writeLine' (prem p) "\\prem" [] []
  and_el f = writeLine' (and_el f) "\\land e_1" [f] []
  and_er f = writeLine' (and_er f) "\\land e_2" [f] []
  and_i f1 f2 = writeLine' (and_i f1 f2) "\\land i" [f1,f2] []
  imp_i cf = writeLine' (imp_i cf) "\\rightarrow i" [] [cf]
  imp_e f1 f2 = writeLine' (imp_e f1 f2) "\\rightarrow e" [f1,f2] []
  bot_e f p = writeLine' (bot_e f p) "\\bot e" [f] []
  not_e f1 f2 = writeLine' (not_e f1 f2) "\\lnot e" [f1,f2] []
  nn_e f = writeLine' (nn_e f) "\\lnot\\lnot e" [f] []
  not_i cf = writeLine' (not_i cf) "\\lnot i" [] [cf]
  or_e f cf1 cf2 = writeLine' (or_e f cf1 cf2) "\\lor e" [f] [cf1,cf2]
  or_il f p = writeLine' (or_il f p) "\\lor i_1" [f] []
  or_ir p f = writeLine' (or_ir p f) "\\lor i_2" [f] []
