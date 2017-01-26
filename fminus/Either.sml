
structure Either = struct

datatype ('a, 'b) either = VAL of 'a | ERR of 'b;

fun unzipEither elist =
  let fun uzacc [] vals errs = (rev vals, rev errs)
        | uzacc ((VAL v)::rest) vals errs =
          uzacc rest (v::vals) errs
        | uzacc ((ERR e)::rest) vals errs =
          uzacc rest vals (e::errs)
  in
      uzacc elist [] []
  end;

(** Folds in vals, returns list of errs *)
fun foldEither f b0 alist =
  let fun fe' b [] errs = (rev b, rev errs)
        | fe' b ((VAL a)::rest) errs = fe' (f (a, b)) rest errs
        | fe' b ((ERR e)::rest) errs = fe' b rest (e::errs)
  in fe' b0 alist []
  end
end
(*
- foldl;
> val ('a, 'b) it = fn : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
 - b is the symbol table, a is the decl
*)
