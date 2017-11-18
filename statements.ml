let name2pairs acc (name, th) =
  let acc =
    if is_conj (concl th) then
      let fold_fun (no, acc) th = (no + 1, (name ^ "_conjunct" ^ (string_of_int no), th) :: acc) in
      snd (List.fold_left fold_fun (0, acc) (CONJUNCTS th))
    else acc
  in (name, th) :: acc
;;
let dump_theorems () =
  let oc = open_out "theorems" in
  let all_thms = List.fold_left name2pairs [] !theorems in
  output_value oc (map (fun (a,b) -> (a, dest_thm b)) all_thms);
  close_out oc
;;
dump_theorems ();;
