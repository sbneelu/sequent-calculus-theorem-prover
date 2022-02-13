module Peirce where

import Prover (atom, nt, proofToJson, prove, (&&&), (-->), (|||))

main :: IO ()
main =
  let p = atom "P"
      q = atom "Q"
   in let prop = ((p --> q) --> p) --> p
       in let proof = prove prop
           in print (proofToJson proof)
