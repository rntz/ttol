structure Util = struct
  fun both f (x,y) = (f x, f y)
  fun on f proj = f o both proj
end

structure HS = struct
  local open Util in

  (* debruijn indices *)
  type var = int
  val vareq : var * var -> bool = op=

  datatype tp = TArr of tp * tp
              | TProd of tp * tp
              | TInt

  val tpeq : tp * tp -> bool = op=

  datatype proj = L | R
  fun proj L (x,_) = x
    | proj R (_,y) = y

  datatype exp = ELam of tp * exp | EApp of exp * exp
               | EPair of exp * exp | EProj of proj * exp
               | EVar of var
               | EInt of int

  datatype term = MLam of tp * term (* binds *)
                | MPair of term * term
                | MInt of int
                | MAtom of atom

       and atom = RVar of var
                | RApp of atom * term
                | RProj of proj * atom


  (* type checking *)
  exception TypeError of string
  type cx = tp list
  fun cxExtend cx tp = tp::cx

  fun cxLookup [] _ = raise TypeError "unbound variable"
    | cxLookup (x::_) 0 = x
    | cxLookup (_::xs) n = cxLookup xs (n-1)

  fun checkType t1 t2 msg =
      (tpeq (t1,t2) orelse raise TypeError msg; ())

  fun inferTerm cx (MLam (argty, body)) =
      TArr (argty, inferTerm (cxExtend cx argty) body)
    | inferTerm cx (MPair p) = on TProd (inferTerm cx) p
    | inferTerm cx (MInt _) = TInt
    | inferTerm cx (MAtom a) = inferAtom cx a

  and inferAtom cx (RVar v) = cxLookup cx v
    | inferAtom cx (RApp (a,m)) =
      let val mt = inferTerm cx m
      in case inferAtom cx a
          of TArr (t1,t2) => (checkType t1 mt "ill-typed function argument"; t2)
           | _ => raise TypeError "application of non-function"
      end
    | inferAtom cx (RProj (d,a)) =
      (case inferAtom cx a
        of TProd p => proj d p
         | _ => raise TypeError "projection from non-pair")

  fun inferExp cx (ELam (argty, body)) =
      TArr(argty, inferExp (cxExtend cx argty) body)
    | inferExp cx (EPair p) = on TProd (inferExp cx) p
    | inferExp cx (EInt _) = TInt
    | inferExp cx (EVar v) = cxLookup cx v
    | inferExp cx (EApp (f,a)) =
      let val at = inferExp cx a
      in case inferExp cx f
          of TArr (t1,t2) => (checkType t1 at "ill-typed function argument"; t2)
           | _ => raise TypeError "application of non-function"
      end
    | inferExp cx (EProj (d,e)) =
      (case inferExp cx e
        of TProd p => proj d p
         | _ => raise TypeError "projection from non-pair")


  (* substitution *)
  type subst = var * term
  fun lift (v,t) = (v+1,t)

  datatype term_or_atom = M of term | R of atom

  fun atomize (M (MAtom a)) = R a
    | atomize e = e

  (* substTerm : subst -> term -> term
   * substAtom : subst -> atom -> term_or_atom
   *)
  fun substTerm s (MLam (ty, body)) = MLam (ty, substTerm (lift s) body)
    | substTerm s (MPair p) = on MPair (substTerm s) p
    | substTerm s (MInt i) = MInt i
    | substTerm s (MAtom a) = (case substAtom s a
                                of M t => t
                                 | R a' => MAtom a')

  and substAtom (v,t) (r as RVar v') =
      if vareq (v,v') then M t else R r
    | substAtom s (RApp (r,m)) =
      let val m' = substTerm s m
      in case atomize (substAtom s r)
          of R r' => R (RApp (r', m'))
           | M (MLam (_,e)) =>
             (* this is the hereditary substitution case. *)
             M (substTerm (0,m') e)
           | M _ => raise TypeError "impossible"
      end
    | substAtom s (RProj (d,r)) =
      (case atomize (substAtom s r)
        of R r' => R (RProj (d,r'))
         | M (MPair p) => M (proj d p)
         | M _ => raise TypeError "impossible")


  (* converting exps to terms (ie. canonicalizing) *)
  (* canonicalize : exp -> term *)
  fun canonicalize (EInt i) = MInt i
    | canonicalize (ELam (t,e)) = MLam (t, canonicalize e)
    | canonicalize (EPair p) = on MPair canonicalize p
    | canonicalize (EVar v) = MAtom (RVar v)
    | canonicalize (EApp p) =
      (case both canonicalize p
        of (MLam (_, body), arg) => substTerm (0,arg) body
         | (MAtom r, arg) => MAtom (RApp (r, arg))
         | _ => raise TypeError "impossible")
    | canonicalize (EProj (d,e)) =
      (case canonicalize e
        of MPair p => proj d p
         | MAtom r => MAtom (RProj (d,r))
         | _ => raise TypeError "impossible")

  end                           (* local open Util in *)
end
