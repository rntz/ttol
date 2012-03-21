structure Util = struct
  fun curry f x y = f (x,y)
  fun uncurry f (x,y) = f x y
  fun flip f x y = f y x
  fun swap (x,y) = (y,x)

  fun both f (x,y) = (f x, f y)
  fun on f proj = f o both proj

  fun consif true x xs = x::xs
    | consif false _ xs = xs

  fun treeFoldList empty leaf node =
      let fun tree _ [] = (empty, [])
            | tree 1 (x::xs) = (leaf x, xs)
            | tree n L = let val nleft = n div 2
                             val (left, L) = tree nleft L
                             val (right, L) = tree (n - nleft) L
                         in (node (left, right), L)
                         end
      in fn L => let val (t,[]) = tree (length L) L in t end
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
      let fun join (x, L as y::_) =
              if cmp (x,y) = EQUAL then L else x::L
            | join (x, []) = [x]
      in foldr join nil o sort cmp
      end

end
