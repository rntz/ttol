structure Util = struct
  datatype ('a,'b) sum = A of 'a | B of 'b

  datatype proj = L | R
  fun proj L (x,_) = x
    | proj R (_,y) = y

  fun id x = x
  fun curry f x y = f (x,y)
  fun uncurry f (x,y) = f x y
  fun flip f x y = f y x
  fun swap (x,y) = (y,x)

  fun both f (x,y) = (f x, f y)
  fun on f proj = f o both proj

  fun mapFst f (x,y) = (f x, y)
  fun mapSnd f (x,y) = (x, f y)

  fun raiseIf e true = raise e
    | raiseIf _ false = ()

  fun raiseUnless e c = raiseIf e (not c)

  fun consif true x xs = x::xs
    | consif false _ xs = xs

  fun treeFoldList empty leaf node =
      let fun tree _ [] = (empty, [])
            | tree 1 (x::xs) = (leaf x, xs)
            | tree n l = let val nleft = n div 2
                             val (left, l) = tree nleft l
                             val (right, l) = tree (n - nleft) l
                         in (node (left, right), l)
                         end
      in fn l => let val (t,[]) = tree (length l) l in t end
      end

  fun sort cmp =
      let fun merge (l, []) = l
            | merge ([], l) = l
            | merge (X as x::xs, Y as y::ys) =
              (case cmp (x,y)
                of EQUAL => x::y::merge (xs, ys)
                 | LESS => x::merge (xs, Y)
                 | GREATER => y::merge (X, ys))
      in treeFoldList [] (fn x => [x]) merge
      end

  fun uniq cmp =
      let fun join (x, ys as y::_) =
              if cmp (x,y) = EQUAL then ys else x::ys
            | join (x, []) = [x]
      in foldr join nil o sort cmp
      end

end
