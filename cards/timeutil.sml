(** Timeutil.sml
  * Time a function
  * Author: Jason Perry *)

(** Usage (MOSML): - load "Timer"; use "Timeutil.sml"; *)

(* actually want it to take a lazy parameter *)
fun timeFn f = let val timer = Timer.startCPUTimer ()
               in (f ();
                   Timer.checkCPUTimes timer)
               end

