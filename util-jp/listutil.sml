(** Quick 0-n range function. *)
fun range n = List.tabulate (n, fn x => x);
fun range2 (a,b) = List.tabulate (b - a, fn x => x + a);
