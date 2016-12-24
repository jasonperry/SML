(* Units required:
 * CommandLine, Int, Time, Random, Binarymap, "deck.sml" *)

signature CARDGAME = sig
    type gstate; (* maybe deck and tableau explicitly? multiple decks? *)
    type move; (* move representation, i.e. (from, to) *)
    type tableau; (* include? *)
    (* type stock; *) (* for future expansion *)
    type deck = Deck.deck;
    type mover = gstate -> move
                               (* val play: gstate -> ?? *)
end

signature TABLEAU = sig
    type t;
    (* val 'a col = t -> int -> 'a *)
end

(****** UTIL FUNCTIONS ******)
fun argmax f [] = raise Empty
  | argmax f (x::xs) =
    let fun am' f max maxx [] = maxx
          | am' f max maxx (x::xs) =
            let val newval = f x
            in if newval > max
               then am' f newval x xs
               else am' f max maxx xs
            end
    in am' f (f x) x xs
    end

structure AcesUp = struct
(* How about a functor that takes a player...move-making callback! Ha! *)
(* Nah, it's just a function to pass in. But how to constrain its type 
   better? *)

(* Mutable stacks for the tableau might be better than lists. *)
type tableau = Deck.card list array
type game = { deck: Deck.deck, tableau: tableau }
type move = int * int

exception IllegalMove

(* if def smlnj *)
(* fun makerng s = let rng = Random.rand (s, s+17)
                   in fn n => Random.randRange (0, n) rng 
                   end *)
(* ifdef mosml *)  (* aw yeah, closure, uh, uh *)
fun makerng s = let val rng = Random.newgenseed (real s)
                in
                    fn n => Random.range (0, n) rng
                end
(* ifdef mlton *)
(* ifdef polyml *)

fun makeGame s = { deck = Deck.makeDeck (makerng s),
                   tableau = Array.fromList [[],[],[],[]] }: game
                                                                 
(* Should this really be 2 different functions? *)
fun resetGame (g: game) = app (fn i => Array.update (#tableau(g), i, []))
                              [0,1,2,3]
                       
(*  If we were doing more with this we could make an 'add' function. *)      
fun deal {deck, tableau} = 
  let val [a,b,c,d]  = Deck.deal deck 4 (* doesn't need to check empty case *)
  in
      (Array.update(tableau, 0, a::Array.sub(tableau,0));
       Array.update(tableau, 1, b::Array.sub(tableau,1));
       Array.update(tableau, 2, c::Array.sub(tableau,2));
       Array.update(tableau, 3, d::Array.sub(tableau,3)) )
  end


(** Move a card from a non-empty column to an empty column. *)
fun move (tab: tableau) (from, to) =
  let val col1 = Array.sub(tab, from)
      val col2 = Array.sub(tab, to)
  in
      if null col1 orelse not (null col2) then raise IllegalMove
      else (Array.update(tab, to, [hd col1]);
            Array.update(tab, from, tl col1))
  end


fun tableauSize tableau = Array.foldl (fn (col,r) => r + length col) 0 tableau
(* fun showTableau *)

(** Eliminate all possible cards. *)
fun elim (tab: tableau) = 
  let val [col1,col2,col3,col4] = [Array.sub(tab,0),
                                   Array.sub(tab,1),
                                   Array.sub(tab,2),
                                   Array.sub(tab,3)]
      (* perform one elimination pass and remember if any were eliminated. *)
      val elims = Array.foldli
                      (fn (i, col, r) =>
                          if not (null col) andalso
                             ((not (null col1) andalso
                               #suit(hd col) = #suit(hd col1) andalso
                               #rank(hd col) < #rank(hd col1)) orelse
                              (not (null col2) andalso
                               #suit(hd col) = #suit(hd col2) andalso
                               #rank(hd col) < #rank(hd col2)) orelse
                              (not (null col3) andalso
                               #suit(hd col) = #suit(hd col3) andalso
                               #rank(hd col) < #rank(hd col3)) orelse
                              (not (null col4) andalso
                               #suit(hd col) = #suit(hd col4) andalso
                               #rank(hd col) < #rank(hd col4)))
                          then
                              (Array.update(tab, i, tl col); true)
                          else r)
                      false tab
  in if elims then (elim tab orelse true) (* funny avoiding short-ckt *)
     else false
  end

(** Take a mover callback and play a game, returning # cards left in play *)
fun play (game as {deck, tableau})
         (mover: tableau -> (int * int) option) =
  (* function to call the mover function and apply its moves until it's done *)
  let fun moves () =
        case (mover tableau) of
            SOME m => (move tableau m; moves())
          | NONE => ()
      (* After deal, keep moving and eliminating as much as possible. *)
      fun turn () = (moves();
                     if (elim tableau) then turn() else ()) 
      (* My new principle: local recursive functions to factor out unchanging
       * arguments *)
      fun play' () =
        if Deck.cardsLeft deck = 0 then tableauSize tableau
        else 
            (deal game; elim tableau; turn(); play'())
  in (Deck.shuffle (#deck game); play'())
  end 

(* ****************************************************************** *)

type mover = tableau -> int * int option

(* return list of possible moves to the first empty column. *)
(*fun possibleMoves (tab: tableau) = 
  case (Array.findi (fn (i, col) => null col) tableau) of
      NONE => []
   |  SOME (to, _) => 
 *)
                                  
fun noMove tableau = NONE

(* Play an interactive game. This function can do the displaying. Yay! *)
fun interactiveMove (tableau: tableau) = NONE

(* Find first column that has >1 cards and move into the first empty space 
 * Todo: write it in Option-monad style. *)
fun dumbMover (tableau: tableau) =
  case (Array.findi (fn (i, col) => null col) tableau) of
      NONE => NONE
   |  SOME (to, _) => (
      case (Array.findi (fn (i, col) => length col >= 2) tableau) of
          NONE => NONE
       |  SOME (from, _) => SOME (from, to) )

(* Make a move and see how many eliminations it causes *)              
fun tryElim (tab: tableau) (mv: move) =
  let val tcopy = Array.fromList [[],[],[],[]]
  in Array.copy {src=tab, dst=tcopy, di=0};
     move tcopy mv;
     elim tcopy;
     print ("Eliminates " ^ Int.toString (tableauSize tcopy) ^ "\n");
     tableauSize tcopy
  end
             
(* Move the card that will give you the most eliminations. *)
(* Uses 'tryelim' to try a move *)
fun moveMostElims (tab: tableau) = 
  case (Array.findi (fn (i, col) => null col) tab) of
      NONE => NONE
   |  SOME (to, _) =>
      let val colCands = List.filter (fn ind => ind >= 0)
                                     (List.tabulate
                                          (Array.length tab,
                                           fn i => if length (Array.sub(tab, i)) >= 2
                                                   then i else ~1))
          val moveCands = List.map (fn c => (c, to)) colCands
      in if moveCands = [] then NONE
         else (
             (*List.app (fn (from,to) => print ("(" ^ Int.toString from ^ "," ^
                                              Int.toString to ^ ") ")) moveCands;*)
             SOME (argmax (tryElim tab) moveCands))
      end

(* Move card from longest column into first empty space *)
fun moveLongest tableau =
  case (Array.findi (fn (i, col) => null col) tableau) of
      NONE => NONE
   |  SOME (to, _) =>
      let val maxIndex =
              Array.foldli (fn (i, col, maxi) =>
                               if length col > length (Array.sub(tableau, maxi))
                               then i else maxi)
                           0 tableau 
      in if length (Array.sub(tableau, maxIndex)) >= 2
         then SOME (maxIndex, to)
         else NONE
      end

(* Move the card with max rank (so it can eliminate others). 
   moveLongest still does slightly better. *)
fun moveMaxRank (tableau: tableau) =
  case (Array.findi (fn (i, col) => null col) tableau) of
      NONE => NONE
   |  SOME (to, _) =>
      let val (maxrank, maxi) =
              Array.foldli (fn (i, col, (maxrank,maxi)) =>
                               if length col >= 2 andalso
                                  #rank(hd col) > maxrank
                               then (#rank(hd col), i)
                               else (maxrank, maxi))
                           (0,~1) tableau
      in if maxi > ~1
         then SOME (maxi, to)
         else NONE
      end

(* Select a random column with at least 2 cards *)
fun moveRandom (tableau: tableau) =
  case (Array.findi (fn (i, col) => null col) tableau) of
      NONE => NONE
   |  SOME (to, _) =>
      let val rng = makerng (Time.toSeconds (Time.now ()))
                        (*(LargeInt.toInt (LargeInt.mod   (* *SMLNJ* *)
                                             (Time.toSeconds (Time.now ()),
                                              1073741789)) , 0 ) *)
          val candCols = List.filter (fn col =>
                                         length (Array.sub (tableau, col)) >= 2)
                                     [0,1,2,3]
      in if (length candCols) = 0 then NONE
         else if (length candCols) = 1 then SOME (hd candCols, to)
         else 
             let val rind = rng (length candCols)
                     (*Random.randRange (0, (length candCols) - 1) rng *)
             in SOME (List.nth (candCols, rind), to)
             end
      end

fun moveMinRank (tableau: tableau) =
  case (Array.findi (fn (i, col) => null col) tableau) of
      NONE => NONE
   |  SOME (to, _) =>
      let val (minrank, mini) =
              Array.foldli (fn (i, col, (minrank,mini)) =>
                               if length col >= 2 andalso
                                  #rank(hd col) < minrank
                               then (#rank(hd col), i)
                               else (minrank, mini))
                           (0,14) tableau
      in if mini < 14
         then SOME (mini, to)
         else NONE
      end
          
fun moveShortest tableau =
  case (Array.findi (fn (i, col) => null col) tableau) of
      NONE => NONE
   |  SOME (to, _) =>
      let val (minLength, minIndex) =
              Array.foldli (fn (i, col, (minlen, mini)) =>
                               if length col >= 2 andalso
                                  length col < minlen
                               then (length col, i) else (minlen, mini))
                           (14,~1) tableau 
      in if minIndex > ~1
         then SOME (minIndex, to)
         else NONE
      end
       
   
(* Move the first card that exposes an elimination. Use find. *)

(* TODO: move this out to my 'utils' code *)
fun mkStringDict (slist: (string * 'a) list) = 
  List.foldl (fn ((s, v), d) => Binarymap.insert (d, s, v))
             (Binarymap.mkDict String.compare)
             slist
     
val moverMap = mkStringDict [("fromshortest", moveShortest),
                             ("none", noMove),
                             ("interactive", interactiveMove),
                             ("dumb", dumbMover),
                             ("maxelims", moveMostElims),
                             ("fromlongest", moveLongest),
                             ("maxrank", moveMaxRank),
                             ("minrank", moveMinRank),
                             ("random", moveRandom)]

fun getMover s = Binarymap.find (moverMap, s)

end (* structure AcesUp *)

(* game is a win if result of "play" is 4 *)      
(* fun runExper ntrials strat *)

fun playtest seed mover n =
  let val g = AcesUp.makeGame seed
      fun playtest' n sum wins =
        if n = 0 then (sum, wins)
        else (AcesUp.resetGame g;
              let val cardsLeft = AcesUp.play g mover
              in playtest' (n-1) (sum + cardsLeft)
                           (if cardsLeft = 4 then wins+1 else wins)
              end)
  in
      let val (sum, wins) = playtest' n 0 0
      in (real(sum) / real(n), wins, real(wins) / real(n))
      end
  end
              
(* main *)
fun main () =
  case CommandLine.arguments () of
      [sd, mv, ng] => let val seed = valOf (Int.fromString sd)
                          val mover = AcesUp.getMover mv
                          val ngames = valOf (Int.fromString ng)
                          val (avgscore, nwins, winrate) =
                              playtest seed mover ngames
                      in
                          print ("wins: " ^ Int.toString nwins
                                 ^ "\naverage: " ^ Real.toString winrate
                                 ^ "\navg score: " ^ Real.toString avgscore
                                 ^ "\n")
                      end
   | _ => print "Usage: acesup <seed> <mover> <ngames>\n"

val _ = main ()
