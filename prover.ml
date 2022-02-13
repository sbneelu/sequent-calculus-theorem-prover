type proposition =
| Atom of string
| Not of proposition
| Or of proposition * proposition
| And of proposition * proposition
| Implies of proposition * proposition;;

type sequent = Sequent of (proposition list * proposition list);;

type rule =
| Not_l | Not_r
| And_l | And_r
| Or_l | Or_r
| Implies_l | Implies_r;;

type proof = Basic of sequent | Invalid of sequent | Rule of (rule * sequent * proof list);;

let list_without list without = List.filter (fun x -> List.for_all (fun y -> x <> y) without) list;;

let rec remove_duplicates = function
| [] -> []
| x :: xs ->
    let new_xs = remove_duplicates xs in
    if List.exists (fun y -> x = y) new_xs then new_xs else x :: new_xs;;

let combine_lists l1 l2 =
    let rec combine_lists_aux xs ys =
        match ys with
        | [] -> xs
        | y :: ys -> y :: (combine_lists_aux xs ys) in
    remove_duplicates (combine_lists_aux l1 l2);;

let expand_not_l (Sequent(assumps, goals)) =
    let not_assumps = List.filter (fun x -> match x with Not _ -> true | _ -> false) assumps in
    Sequent(
        list_without assumps not_assumps,
        combine_lists goals (List.map (fun a -> match a with Not a -> a | a -> a) not_assumps)
        (*  a -> a above is for the sake of complete pattern matching. But all not_assumps will
         *  be of the form Not _.
         *)
    );;

let expand_not_r (Sequent(assumps, goals)) =
    let not_goals = List.filter (fun x -> match x with Not _ -> true | _ -> false) goals in
    Sequent(
        combine_lists assumps (List.map (fun a -> match a with Not a -> a | a -> a) not_goals),
        list_without goals not_goals
    );;

let expand_and_l (Sequent(assumps, goals)) =
    let and_assumps = List.filter (fun x -> match x with And _ -> true | _ -> false) assumps in
    Sequent(
        combine_lists (list_without assumps and_assumps) (List.fold_left combine_lists [] (List.map (fun x -> match x with And(a, b) -> [a; b] | _ -> []) and_assumps)),
        goals
    );;

let expand_and_r (Sequent(assumps, goals)) =
    let and_goal = List.find (fun x -> match x with And _ -> true | _ -> false) goals in
    match and_goal with
    | And (p, q) ->
        let new_goals = list_without goals [and_goal] in
        [
            Sequent(
                assumps,
                remove_duplicates (p :: new_goals)
            );
            Sequent(
                assumps,
                remove_duplicates (q :: new_goals)
            )
        ]
    | _ -> [];;

let expand_or_l (Sequent(assumps, goals)) =
    let or_assump = List.find (fun x -> match x with Or _ -> true | _ -> false) assumps in
    match or_assump with
    | Or (p, q) ->
        let new_assumps = list_without assumps [or_assump] in
        [
            Sequent(
                remove_duplicates (p :: new_assumps),
                goals
            );
            Sequent(
                remove_duplicates (q :: new_assumps),
                goals
            )
        ]
    | _ -> [];;

let expand_or_r (Sequent(assumps, goals)) =
    let or_goals = List.filter (fun x -> match x with Or _ -> true | _ -> false) goals in
    Sequent(
        assumps,
        combine_lists (list_without goals or_goals) (List.fold_left combine_lists [] (List.map (fun x -> match x with Or(a, b) -> [a; b] | _ -> []) or_goals))
    );;

let expand_implies_l (Sequent(assumps, goals)) =
    let implies_assump = List.find (fun x -> match x with Implies _ -> true | _ -> false) assumps in
    match implies_assump with
    | Implies (p, q) ->
        let new_assumps = list_without assumps [implies_assump] in
        [
            Sequent(
                new_assumps,
                remove_duplicates (p :: goals)
            );
            Sequent(
                remove_duplicates (q :: new_assumps),
                goals
            )
        ]
    | _ -> [];;

let expand_implies_r (Sequent(assumps, goals)) =
    let implies_goals = List.filter (fun x -> match x with Implies _ -> true | _ -> false) goals in
    Sequent(
        combine_lists assumps (List.map (fun x -> match x with Implies(a, b) -> a | _ -> x) implies_goals),
        combine_lists (list_without goals implies_goals) (List.map (fun x -> match x with Implies(a, b) -> b | _ -> x) implies_goals)
    );;

let all_atoms = List.for_all (fun x -> match x with Atom _ -> true | _ -> false);;

let rec have_intersection xs ys =
    match ys with
    | [] -> false
    | y :: ys -> List.exists (fun x -> x = y) xs || have_intersection xs ys;;

let prove_sequent (Sequent(assumps, goals)) =
    let rec prove_aux (Sequent(assumps, goals)) =
        let sequent = Sequent(assumps, goals) in
        if all_atoms assumps && all_atoms goals then (
            if have_intersection assumps goals then Basic(sequent)
            else Invalid(sequent)
        )
        else if List.exists (fun x -> match x with Not _ -> true | _ -> false) assumps then
            Rule(Not_l, sequent, [prove_aux (expand_not_l sequent)])
        else if List.exists (fun x -> match x with Not _ -> true | _ -> false) goals then
            Rule(Not_r, sequent, [prove_aux (expand_not_r sequent)])
        else if List.exists (fun x -> match x with And _ -> true | _ -> false) assumps then
            Rule(And_l, sequent, [prove_aux (expand_and_l sequent)])
        else if List.exists (fun x -> match x with And _ -> true | _ -> false) goals then
            Rule(And_r, sequent, List.map (fun x -> prove_aux x) (expand_and_r sequent))
        else if List.exists (fun x -> match x with Or _ -> true | _ -> false) assumps then
            Rule(Or_l, sequent, List.map (fun x -> prove_aux x) (expand_or_l sequent))
        else if List.exists (fun x -> match x with Or _ -> true | _ -> false) goals then
            Rule(Or_r, sequent, [prove_aux (expand_or_r sequent)])
        else if List.exists (fun x -> match x with Implies _ -> true | _ -> false) assumps then
            Rule(Implies_l, sequent, List.map (fun x -> prove_aux x) (expand_implies_l sequent))
        else if List.exists (fun x -> match x with Implies _ -> true | _ -> false) goals then
            Rule(Implies_r, sequent, [prove_aux (expand_implies_r sequent)])
        else
            Invalid(sequent) (* This shouldn't ever be reached *)
        in
    prove_aux (Sequent((remove_duplicates assumps), (remove_duplicates goals)));;

let prove proposition = prove_sequent (Sequent([], [proposition]));;

let rec proposition_to_json = function
| Atom a -> "{\"type\": \"atom\", \"proposition\": \"" ^ a ^ "\"}"
| Not a -> "{\"type\": \"not\", \"proposition\": " ^ (proposition_to_json a) ^ "}"
| And (a, b) -> "{\"type\": \"and\", \"propositions\": [" ^ (proposition_to_json a) ^ ", " ^ (proposition_to_json b) ^ "]}"
| Or (a, b) -> "{\"type\": \"or\", \"propositions\": [" ^ (proposition_to_json a) ^ ", " ^ (proposition_to_json b) ^ "]}"
| Implies (a, b) -> "{\"type\": \"implies\", \"propositions\": [" ^ (proposition_to_json a) ^ ", " ^ (proposition_to_json b) ^ "]}";;

let rule_to_string = function
| Not_l -> "Not_l"
| Not_r -> "Not_r"
| And_l -> "And_l"
| And_r -> "And_r"
| Or_l -> "Or_l"
| Or_r -> "Or_r"
| Implies_l -> "Implies_l"
| Implies_r -> "Implies_r";;

let sequent_to_json (Sequent (assumps, goals)) =
    let assumps_json = "[" ^ ((List.map proposition_to_json assumps) |> String.concat ",") ^ "]" in
    let goals_json = "[" ^ ((List.map proposition_to_json goals) |> String.concat ",") ^ "]" in
    "{\"assumps\": " ^ assumps_json ^ ", \"goals\": " ^ goals_json ^ "}";;

let rec proof_to_json = function
| Basic sequent -> "{\"type\": \"basic\", \"sequent\": " ^ sequent_to_json sequent ^ "}"
| Invalid sequent -> "{\"type\": \"invalid\", \"sequent\": " ^ sequent_to_json sequent ^ "}"
| Rule(rule, sequent, proof_list) ->
    let rule_string = rule_to_string rule in
    let sequent_json = sequent_to_json sequent in
    let proof_json = "[" ^ ((List.map proof_to_json proof_list) |> String.concat ",") ^ "]" in
    "{\"type\": \"" ^ rule_string ^ "\", \"sequent\": " ^ sequent_json ^ ", \"proof\": " ^ proof_json ^ "}";;
