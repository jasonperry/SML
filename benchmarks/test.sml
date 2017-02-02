
(* the overloaded arithmetic operators are not really polymorphic.
   if you don't tell it, it assumes a default type (int). *)
fun cube (x:real) = 
    x * x * x

fun min3 (a,b,c) = 
    if a < b then  (* put "then" on the same line, like an opening bracket *)
        if a < c then a
        else c 
    else (* always start a new "if" on a new line *)
        if b < c then b
        else c

fun thrd (a::b::c::rest) = c
(*  | thrd _ = () (* Nope! makes it 'unit list' *) *)
(*  | thrd _ = nil (* type 'list list' *) *)

fun rev3 (a, b, c) = (c, b, a)

fun thirdc (s) = hd (tl (tl (explode s)))

fun third (s) = 
    let val (_::_::c::rest) = explode s
    in c
    end 

fun thirdc (s) = 
    case (explode s) of 
        _::_::c::rest => c
      | _ => chr 0

fun cycle (a::rest) = rest @ [a]
| cycle _ = [] (* type vars not generalized ... instantiated to dummy types *)

(* exercise 3.1.2 *)

fun bignsmall (a,b,c) = 
    if a < b then
        if b < c then (a,c)
        else (* b biggest *)
            if a < c then (a,b) 
            else (b,c)
    else 
        if c > a then (b,c) (* c biggest *)
        else 
            if c < b then (a,c)
            else (a,b)

fun sort3 (a,b,c) = 
    if a < b then
        if b < c then (a,b,c)
        else 
            if a < c then (a, c, b)
            else (c, a, b)
    else (* b < a *)
        if c < b then (c, b, a)
        else 
            if a < c then (b, a, c)
            else (b, c, a)

(* this was harder than it seemed it should be. *)
fun round10 (r:real) = 
    (real (floor (r * 10.0 + 0.5))) / 10.0

fun del2nd (a::b::rest) = a::rest

fun choose (n,r) = 
    if r = 0 orelse n = r then 1
    else 
        choose(n-1,r) + choose(n-1,r-1)

fun choosec n r = 
    if r = 0 orelse n = r then 1
    else 
        choosec (n-1) r + choosec (n-1) (r-1)

fun test1 () = 
    let val timer = Timer.startCPUTimer () (* need the unit argument *)
    (* is the semantics of tupling and sequencing the same? *)
    in (choose(31,16); Timer.checkCPUTimer timer)
    end
(* avg: 4814130 usec *)

fun test2 () = 
    let val timer = Timer.startCPUTimer ()
    in (choosec 31 16; Timer.checkCPUTimer timer)
    end
(* avg: 4837462 usec: .5% difference - surely not stat. significant *)

(* of course you don't need mutual recursion to take every other element *)
fun alt (a::b::rest) = a::(alt rest)
  | alt l = l

fun main () = print "hello mlton?\n"

(* this is how you do it with mlton (AND sml) *)
val _ = print "hello mlton world\n"
