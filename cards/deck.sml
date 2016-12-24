(* Required units: Int *)

signature DECK = sig
    type deck; (* maybe 'type t = deck' *)
    datatype suit = Club | Diamond | Heart | Spade;
    (* How to abstract, but expose, the card type? 
     * Maybe with a sharing for the other module? *)
    type card = {suit: suit, rank: int}; 
    exception IllegalCard (* Since the rank is an int. *)
    type rngModn = int -> int
    val showCard : card -> string;
    val makeDeck : rngModn -> deck; 
    val cardsLeft : deck -> int;
    val reset : deck -> unit;
    val shuffle : deck -> unit;
    val deal : deck -> int -> card list
end

(* Update 2016-02-23: Take a generic RNG function that takes an integer
 * and stores its own state *)

structure Deck :> DECK = struct
(* Is functorizing a stinky way of making it like objects?
 * Yes, very stinky. State should be stored in the type, not the module.
 * Which is done now. *)

(* Could functorize it by the card type and make it enumerate them
 * all...ha! *)

datatype suit = Club | Diamond | Heart | Spade

(* There's an enum in the mltonlib project, and in SML acapd. *)
type card = {suit: suit, rank: int}
exception IllegalCard
              
type rngModn = int -> int

type deck = {deck: card Vector.vector,
             deckOrder: int Array.array,
             deckPointer: int ref,
             rng: rngModn}

fun showCard (card: card) =
  (if #rank(card) < 11 then Int.toString (#rank(card))
   else case #rank(card) of
            11 => "J"
          | 12 => "Q"
          | 13 => "K"
          | 14 => "A"
          | _ => raise IllegalCard)
  ^
  (case #suit(card) of
       Club => "C"
    |  Diamond => "D"
    |  Heart => "H"
    |  Spade => "S")

(* would be cool to have a tabulate-like function for general records *)
fun makeDeck rng = { deck = Vector.fromList [
                         {suit=Club, rank=2}, (* aces high *)
                         {suit=Club, rank=3},
                         {suit=Club, rank=4},
                         {suit=Club, rank=5},
                         {suit=Club, rank=6},
                         {suit=Club, rank=7},
                         {suit=Club, rank=8},
                         {suit=Club, rank=9},
                         {suit=Club, rank=10},
                         {suit=Club, rank=11},
                         {suit=Club, rank=12},
                         {suit=Club, rank=13},
                         {suit=Club, rank=14},
                         {suit=Diamond, rank=2},
                         {suit=Diamond, rank=3},
                         {suit=Diamond, rank=4},
                         {suit=Diamond, rank=5},
                         {suit=Diamond, rank=6},
                         {suit=Diamond, rank=7},
                         {suit=Diamond, rank=8},
                         {suit=Diamond, rank=9},
                         {suit=Diamond, rank=10},
                         {suit=Diamond, rank=11},
                         {suit=Diamond, rank=12},
                         {suit=Diamond, rank=13},
                         {suit=Diamond, rank=14},
                         {suit=Heart, rank=2},
                         {suit=Heart, rank=3},
                         {suit=Heart, rank=4},
                         {suit=Heart, rank=5},
                         {suit=Heart, rank=6},
                         {suit=Heart, rank=7},
                         {suit=Heart, rank=8},
                         {suit=Heart, rank=9},
                         {suit=Heart, rank=10},
                         {suit=Heart, rank=11},
                         {suit=Heart, rank=12},
                         {suit=Heart, rank=13},
                         {suit=Heart, rank=14},
                         {suit=Spade, rank=2},
                         {suit=Spade, rank=3},
                         {suit=Spade, rank=4},
                         {suit=Spade, rank=5},
                         {suit=Spade, rank=6},
                         {suit=Spade, rank=7},
                         {suit=Spade, rank=8},
                         {suit=Spade, rank=9},
                         {suit=Spade, rank=10},
                         {suit=Spade, rank=11},
                         {suit=Spade, rank=12},
                         {suit=Spade, rank=13},
                         {suit=Spade, rank=14} ],
                     deckOrder = Array.tabulate (52, fn n => n),
                     deckPointer = ref 0,
                     rng = rng }

fun cardsLeft (deck: deck) = 52 - !(#deckPointer deck)

fun reset (deck: deck) = (#deckPointer deck) := 0     

(* shuffle using the swap-index method...not uniform? *)
fun shuffleArray (rng: rngModn) a =
  let fun shuf' i0 = 
        if i0 >= Array.length a - 1 then ()
        else 
            let val tmp = Array.sub(a, i0)
                val ix = (rng (52 - i0)) + i0 (* Random.randInt rng mod (52 - i0) + i0 *)
            in (Array.update (a, i0, Array.sub(a, ix));
                Array.update (a, ix, tmp);
                shuf' (i0+1))
            end
  in shuf' 0
  end

(** Always reset the pointer before shuffling to prevent inconsistent output 
  * (Could also shuffle only above the pointer, but YAGNI) *)
fun shuffle deck = (reset deck; shuffleArray (#rng deck) (#deckOrder deck))

fun deal _ 0 = []
  | deal (deck as {deck=d,
           deckOrder=order,
           deckPointer=pointer, rng=r}) n =
    if !pointer = Vector.length d then []
    else
        let val ix = !pointer in
            (pointer := !pointer + 1;
             Vector.sub (d, Array.sub (order, ix)) :: deal deck (n-1)
            )
        end
        
end

