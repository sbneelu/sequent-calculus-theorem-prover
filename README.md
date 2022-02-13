# Propositional Logic Theorem Prover using Sequent Calculus

A propositional logic theorem prover using [sequent calculus](https://en.wikipedia.org/wiki/Sequent_calculus) with Haskell and OCaml implementations.

The provers are in `Prover.hs` and `prover.ml`, with Peirce's law [((P -> Q) -> P) -> P] as an example in `Peirce.hs` and `peirce.ml`.

## Proposition construction

Propositions can be constructed in identical ways in the Haskell and OCaml implementations.

- The `atom` function can be used to create atoms. For example, `p = atom "P"` sets `p = Atom "P"` and `q = atom "Q"` sets `q = Atom "Q"`.
- The `nt` function can be used to negate a proposition. For example, `np = nt p` sets `np = Not (Atom "P")`.
- The `&&&` infix can be used to take the conjunction of two propositions. For example, `p &&& q = And(Atom "P", Atom "Q")`.
- The `&&&` infix can be used to take the disjunction of two propositions. For example, `p ||| q = Or(Atom "P", Atom "Q")`.
- The `-->` infix can be used to create an implication between two propositions. For example, `p --> q = Implies(Atom "P", Atom "Q")`.

## Proof

Both the Haskell and OCaml implementations have a `prove` function which takes in a `Proposition` and returns a `Proof`.

If the proposition is a tautology, the proof contains a full valid proof tree with `Basic` proof steps at the leaves. If the proposition is not a tautology, the proof has `Invalid` proof steps at the leaves.

## Sequents, Rules and Proof Steps

See the type definitions for these near the top of `Prover.hs` and `prover.ml` to see how these are structured. For `Sequent`s, the structure is a pair containing the assumption list and the goal list.

## Exporting to JSON

Both the Haskell and OCaml implementations have a function which takes in a `Proof` and returns a JSON `String`. In Haskell, this function is called `proofToJson` and in OCaml it is called `proof_to_json`.

An example JSON for Peirce's law is in `peirce.json`.