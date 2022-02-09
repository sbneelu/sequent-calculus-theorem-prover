#use "prover.ml";;

let main() =
    let p = Atom "P" in
    let q = Atom "Q" in
    let prop = Implies(Implies(Implies(p, q), p), p) in
    let proof = prove prop in
    print_endline (proof_to_json proof);;

main();;