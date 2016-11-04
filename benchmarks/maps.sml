(* testing the Mosml standard library map implementations *)

(* load "Int"; load "Binarymap"; load "Intmap"; load "Redblackmap"*)

val pairs = [(4, "Bob"), (5, "Sally"), (1, "Fred"), (564873, "Tom"),
             (99, "Mildredghumperdink")]

(* why are they not functorized in the library? *)
(* Module names seem not to be case sensitive ?! *)
fun list2dict dict0 pairs insertfn =
  List.foldl (fn ((k,v), dict) => insertfn (dict, k, v)) dict0 pairs

val emptyb : (int, string) Binarymap.dict = Binarymap.mkDict Int.compare;
val emptyi : string Intmap.intmap = Intmap.empty ();
val emptrb : (int, string) Redblackmap.dict = Redblackmap.mkDict Int.compare;
val emptsp : (int, string) Splaymap.dict = Splaymap.mkDict Int.compare;

val bdict = list2dict emptyb pairs Binarymap.insert;
val rbdict = list2dict emptrb pairs Redblackmap.insert;
val spdict = list2dict emptsp pairs Splaymap.insert;

(* Is it already functorized, because it calls every type 'dict'?
 * Can I just open all four and it knows which one to use? No. *)
