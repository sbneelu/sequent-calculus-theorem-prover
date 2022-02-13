{-# LANGUAGE LambdaCase #-}
module Prover where

import Data.List (intersect, find, intercalate)

data Proposition =
    Atom String
    | Not Proposition
    | Or (Proposition, Proposition)
    | And (Proposition, Proposition)
    | Implies (Proposition, Proposition)
    deriving (Eq, Show)

newtype Sequent = Sequent([Proposition], [Proposition]) deriving Show

data Rule = NotL | NotR | OrL | OrR | AndL | AndR | ImpliesL | ImpliesR deriving Show

data Proof =
    Basic Sequent
    | Invalid Sequent
    | Step (Rule, Sequent, [Proof])
    deriving Show

listWithout list without = filter (`notElem` without) list

removeDuplicates xs = case xs of
    [] -> []
    x : xs ->
        let newXs = removeDuplicates xs in
            if x `elem` xs then newXs else x : newXs

combineLists l1 l2 = removeDuplicates (l1 ++ l2)

expandNotL (Sequent(assumps, goals)) =
    let notAssumps = filter (\case {Not _ -> True; _ -> False}) assumps in
        Sequent(
            listWithout assumps notAssumps,
            combineLists goals (map (\case {Not a -> a; a -> a}) notAssumps)
        )

expandNotR (Sequent(assumps, goals)) =
    let notGoals = filter (\case {Not _ -> True; _ -> False}) goals in
        Sequent(
            combineLists assumps (map (\case {Not a -> a; a -> a}) notGoals),
            listWithout goals notGoals
        )

expandAndL (Sequent(assumps, goals)) =
    let andAssumps = filter (\case {And _ -> True; _ -> False}) assumps in
    Sequent(
        combineLists
            (listWithout assumps andAssumps)
            (foldl combineLists [] (map (\case {And(a, b) -> [a, b]; _ -> []}) andAssumps)),
        goals
    )

expandAndR (Sequent(assumps, goals)) =
    case find (\case {And _ -> True; _ -> False}) goals of
        Just (And (p, q)) ->
            let newGoals = listWithout goals [And(p, q)] in
                [
                    Sequent(
                        assumps,
                        removeDuplicates (p : newGoals)
                    ),
                    Sequent(
                        assumps,
                        removeDuplicates (q : newGoals)
                    )
                ]
        _ -> []

expandOrL (Sequent(assumps, goals)) =
    case find (\case {Or _ -> True; _ -> False}) assumps of
        Just (Or (p, q)) ->
            let newAssumps = listWithout assumps [Or(p, q)] in
                [
                    Sequent(
                        removeDuplicates (p : newAssumps),
                        goals
                    ),
                    Sequent(
                        removeDuplicates (p : newAssumps),
                        goals
                    )
                ]
        _ -> []

expandOrR (Sequent(assumps, goals)) =
    let orGoals = filter (\case {Or _ -> True; _ -> False}) goals in
    Sequent(
        assumps,
        combineLists
            (listWithout goals orGoals)
            (foldl combineLists [] (map (\case {Or(a, b) -> [a, b]; _ -> []}) orGoals))
    )

expandImpliesL (Sequent(assumps, goals)) =
    case find (\case {Implies _ -> True; _ -> False}) assumps of
        Just (Implies (p, q)) ->
            let newAssumps = listWithout assumps [Implies(p, q)] in
                [
                    Sequent(
                        newAssumps,
                        removeDuplicates (p : goals)
                    ),
                    Sequent(
                        removeDuplicates (q : newAssumps),
                        goals
                    )
                ]
        _ -> []

expandImpliesR (Sequent(assumps, goals)) =
    let impliesGoals = filter (\case {Implies _ -> True; _ -> False}) goals in
        Sequent(
            combineLists assumps (map (\case {Implies(a, b) -> a; x -> x}) impliesGoals),
            combineLists (listWithout goals impliesGoals) (map (\case {Implies(a, b) -> b; x -> x}) impliesGoals)
        )

allAtoms :: [Proposition] -> Bool
allAtoms = all (\case {Atom _ -> True; _ -> False})

haveIntersection xs ys = not (null (xs `intersect` ys))

proveSequent (Sequent(assumps, goals)) =
    let proveAux (Sequent(assumps, goals)) =
            let sequent = Sequent(assumps, goals) in
            if allAtoms assumps && allAtoms goals then (
                if haveIntersection assumps goals then Basic sequent
                else Invalid sequent
            )
            else if any (\case {Not _ -> True; _ -> False}) assumps then
                Step(NotL, sequent, [proveAux (expandNotL sequent)])
            else if any (\case {Not _ -> True; _ -> False}) goals then
                Step(NotR, sequent, [proveAux (expandNotR sequent)])
            else if any (\case {And _ -> True; _ -> False}) assumps then
                Step(AndL, sequent, [proveAux (expandAndL sequent)])
            else if any (\case {And _ -> True; _ -> False}) goals then
                Step(AndR, sequent, map proveAux (expandAndR sequent))
            else if any (\case {Or _ -> True; _ -> False}) assumps then
                Step(OrL, sequent, map proveAux (expandOrL sequent))
            else if any (\case {Or _ -> True; _ -> False}) goals then
                Step(OrR, sequent, [proveAux (expandOrR sequent)])
            else if any (\case {Implies _ -> True; _ -> False}) assumps then
                Step(ImpliesL, sequent, map proveAux (expandImpliesL sequent))
            else if any (\case {Implies _ -> True; _ -> False}) goals then
                Step(ImpliesR, sequent, [proveAux (expandImpliesR sequent)])
            else
                Invalid sequent
    in proveAux (Sequent(removeDuplicates assumps, removeDuplicates goals))

prove proposition = proveSequent (Sequent([], [proposition]))

propositionToJson prop = case prop of
    Atom a -> "{\"type\": \"atom\", \"proposition\": \"" ++ a ++ "\"}"
    Not a -> "{\"type\": \"not\", \"proposition\": " ++ propositionToJson a ++ "}"
    And (a, b) -> "{\"type\": \"and\", \"propositions\": [" ++ propositionToJson a ++ ", " ++ propositionToJson b ++ "]}"
    Or (a, b) -> "{\"type\": \"or\", \"propositions\": [" ++ propositionToJson a ++ ", " ++ propositionToJson b ++ "]}"
    Implies (a, b) -> "{\"type\": \"implies\", \"propositions\": [" ++ propositionToJson a ++ ", " ++ propositionToJson b ++ "]}"

ruleToString rule = case rule of
    NotL -> "NotL"
    NotR -> "NotR"
    AndL -> "AndL"
    AndR -> "AndR"
    OrL -> "OrL"
    OrR -> "OrR"
    ImpliesL -> "ImpliesL"
    ImpliesR -> "ImpliesR"

sequentToJson (Sequent (assumps, goals)) =
    let assumpsJson = "[" ++ intercalate "," (map propositionToJson assumps) ++ "]" in
    let goalsJson = "[" ++ intercalate "," (map propositionToJson goals) ++ "]" in
    "{\"assumps\": " ++ assumpsJson ++ ", \"goals\": " ++ goalsJson ++ "}"

proofToJson proof = case proof of 
    Basic sequent -> "{\"type\": \"basic\", \"sequent\": " ++ sequentToJson sequent ++ "}"
    Invalid sequent -> "{\"type\": \"invalid\", \"sequent\": " ++ sequentToJson sequent ++ "}"
    Step(rule, sequent, proofList) ->
        let {ruleString = ruleToString rule; sequentJson = sequentToJson sequent; proofJson = "[" ++ intercalate "," (map proofToJson proofList) ++ "]" } in
            "{\"type\": \"" ++ ruleString ++ "\", \"sequent\": " ++ sequentJson ++ ", \"proof\": " ++ proofJson ++ "}"