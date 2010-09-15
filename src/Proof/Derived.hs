module Proof.Derived(
  mt,
  pbc,
  lem,
  nn_i
) where

import Proof.Monad
import Proof.Language

-- |Modus tollens
mt :: (MonadProof m) =>
      Fact        -- ^ Fact of the form 'a -> b'
   -> Fact        -- ^ Fact of the form 'not b'
   -> m Fact      -- ^ (Proof of) fact of the form 'not a'
mt imp not_psi =
  let (f_phi :-> f_psi) = getFact imp
  in do c_not_phi <- assume f_phi $ \phi -> do
          psi <- imp_e phi imp
          not_e psi not_psi
        not_i c_not_phi


-- |Proof by contradiction
pbc :: (MonadProof m) =>
       CondFact    -- ^ Conditional fact of the form 'Bot', depending on 'not a'
    -> m Fact  -- ^ (Proof of) fact of the form 'a'
pbc cf = derivedRule "\\textsc{pbc}" [] [cf] $ do
  nn_phi <- not_i cf
  nn_e nn_phi


-- |Law of the excluded middle
lem :: (MonadProof m) =>
       Phi         -- Any formula 'a'
    -> m Fact  -- (Proof of) fact of the form 'a :|: Not a'
lem a = derivedRule "\\textsc{lem}" [] [] $ do
  c_n_goal <- assume (Not (a :|: Not a)) $ \n_a_na -> do
    c_a <- assume a $ \a' -> do
      a_na <- or_il a' (Not a)
      not_e a_na n_a_na
    n_a <- not_i c_a
    a_na <- or_ir a n_a
    not_e a_na n_a_na
  nn_goal <- not_i c_n_goal
  nn_e nn_goal


-- |Not-Not introduction
nn_i :: (MonadProof m) =>
        Fact
     -> m Fact
nn_i a = do
  c_na <- assume (Not . getFact $ a) $ \na ->
    not_e a na
  not_i c_na
