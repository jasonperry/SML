(* precompute this (long time to load) *)

(* Won't work on Mosml; has no large int type *)

val biglist = List.tabulate (5000000,
                             fn x => LargeInt.+ (LargeInt.fromInt x,
                                                 LargeInt.toLarge 1))


(* Fold tests.*)
fun bigfoldr () = foldr LargeInt.+ (LargeInt.toLarge 1) biglist

fun bigfoldl () = foldl LargeInt.+ (LargeInt.toLarge 1) biglist 

(* Yes, foldl is much faster. *)
                        
