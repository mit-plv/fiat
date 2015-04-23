let rec printTree = function
  | LabelMap.Raw.Leaf -> ()
  | LabelMap.Raw.Node (t1, _, s, t2, _) ->
      printTree t1;
      List.iter print_char s;
      printTree t2

let _ = printTree compiled
