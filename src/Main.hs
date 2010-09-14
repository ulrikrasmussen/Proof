module Main() where

import Proof

-- Exercise 1.2.5(a)

ex125a p q = do
  c_theo <- assume ((p :-> q) :-> q) $ \pqq -> do
    c_qpp <- assume (q :-> p) $ \qp -> do
      c_p <- assume (Not p) $ \np -> do
        nq <- mt qp np
        npq <- mt pqq nq
        c_q <- assume p $ \p -> do
          bot <- not_e p np
          bot_e bot q
        pq <- imp_i c_q
        not_e pq npq
      pbc c_p
    imp_i c_qpp
  imp_i c_theo


-- Dummy main: Just check the proof of ex125a and output LaTeX if the proof is valid.
main = case checkLatex (ex125a (L"p") (L"q")) of
         Left err -> putStrLn $ "error: " ++ err
         Right res -> putStrLn res
