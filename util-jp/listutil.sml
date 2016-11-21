(** Quick 0-n range function. *)
fun range n = List.tabulate (n, fn x => x);
fun range2 (a,b) = List.tabulate (b - a, fn x => x + a);

(** Map over a list with a function that also takes an index. *)
fun mapi f lst =
  let fun mapi' n [] = []
        | mapi' n (e::es) = (f (e,n))::(mapi' (n+1) es)
  in mapi' 0 lst
  end
