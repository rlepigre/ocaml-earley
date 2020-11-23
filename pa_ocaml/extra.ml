module Option = struct
  let default : 'a -> 'a option -> 'a = fun d eo ->
    match eo with None -> d | Some(e) -> e
end
