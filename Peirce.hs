module Peirce where

import Prover (proofToJson, prove, atom, nt, (&&&), (|||), (-->))

main :: IO ()
main =
  let p = atom "P"
      q = atom "Q"
   in let prop = ((p --> q) --> p) --> p
       in let proof = prove prop
           in print (proofToJson proof)
