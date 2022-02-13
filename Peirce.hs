module Peirce where

import Prover

main :: IO ()
main =
  let p = Atom "P"; q = Atom "Q"
   in let prop = Implies (Implies (Implies (p, q), p), p)
       in let proof = prove prop
           in print (proofToJson proof)
