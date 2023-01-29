


let remove_last_elems (k : int) l =
  let rec remove_fist_elems k l =
    if k = 0 then l else remove_fist_elems (k - 1) @@ List.tl l in
  l |> List.rev |> remove_fist_elems k |> List.rev
