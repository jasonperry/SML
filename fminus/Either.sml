
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

(** Folds in vals to a val, returns list of errs *)
fun foldEither (f: 'a -> 'b -> ('b, 'e) either) b0 alist =
  let fun fe' b [] errs = (b, rev errs)
        | fe' b (a::rest) errs =
          case (f a b)
           of VAL newb => fe' newb rest errs
            | ERR e => fe' b rest (e::errs)
  in fe' b0 alist []
  end
end
(*
- foldl;
> val ('a, 'b) it = fn : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
 - b is the symbol table, a is the decl
*)
