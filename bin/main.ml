open Interp2

let _ =
  if Array.length Sys.argv > 1
  then
    let filename = Sys.argv.(1) in
    match In_channel.(input_all (open_in filename)) with
    | input -> (
        match interp input with
        | Ok v -> print_endline (string_of_value v)
        | Error e -> print_endline ("error: " ^ string_of_error e)
      )
    | exception _ ->
      print_endline ("error: could not read \'" ^ filename ^ "\'")
  else
    print_endline "error: no file given"