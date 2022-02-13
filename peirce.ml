#use "prover.ml";;

let main() =
    let p = atom "P" in
    let q = atom "Q" in
    let prop = ((p --> q) --> p) --> p in
    let proof = prove prop in
    print_endline (proof_to_json proof);;

main();;