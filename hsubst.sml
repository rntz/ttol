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


  (* some syntactic utilities *)
  local
      fun tfv n (MPair (l,r)) acc = tfv n l (tfv n r acc)
        | tfv n (MInt _) acc = acc
        | tfv n (MAtom a) acc = afv n a acc
        | tfv n (MLam (_,t)) acc = tfv (n+1) t acc

      and afv n (RVar v) acc = consif (v >= n) (v-n) acc
        | afv n (RApp (a,t)) acc = afv n a (tfv n t acc)
        | afv n (RProj (d,a)) acc = afv n a acc

      fun efv n (ELam (_,e)) acc = efv (n+1) e acc
        | efv n (EApp (e1,e2)) acc = efv n e1 (efv n e2 acc)
        | efv n (EPair (l,r)) acc = efv n l (efv n r acc)
        | efv n (EProj (d,e)) acc = efv n e acc
        | efv n (EInt _) acc = acc
        | efv n (EVar v) acc = consif (v >= n) (v-n) acc
  in
    fun termFV x = uniq Int.compare (tfv 0 x [])
    fun atomFV x = uniq Int.compare (afv 0 x [])
    fun expFV x = uniq Int.compare (efv 0 x [])
  end

  fun liftTermFromBy from by term =
      let val rterm = liftTermFromBy from by
          val ratom = liftAtomFromBy from by
      in case term
          of MAtom a => MAtom (ratom a)
           | MPair p => on MPair rterm p
           | MInt _ => term
           | MLam (tp, body) =>
             MLam (tp, liftTermFromBy (from+1) by body)
      end

  and liftAtomFromBy from by atom =
      let val ratom = liftAtomFromBy from by
          val rterm = liftTermFromBy from by
      in case atom
          of RVar v => RVar (if v >= from then v + by else v)
           | RApp (a,t) => RApp (ratom a, rterm t)
           | RProj (d,a) => RProj (d, ratom a)
      end

  val liftTermBy = liftTermFromBy 0
  val liftTerm = liftTermBy 1


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


  (* Substitution of one term for one variable. When substituting (v,t) into m,
   * it is a precondition that v is the highest-numbered free variable of m.
   *)
  type subst1 = var * term

  fun checkSubst1Term (v,t) m =
      (List.all (fn v' => v' <= v) (termFV m)
       orelse raise TypeError "not largest free var";
       ())

  fun liftSubst1 (v, t) = (v+1, liftTerm t)

  (* subst1Term : subst1 -> term -> term
   * subst1Atom : subst1 -> atom -> term
   *)
  fun subst1Term s (MLam (ty, body)) =
      MLam (ty, subst1TermC (liftSubst1 s) body)
    | subst1Term s (MPair p) = on MPair (subst1TermC s) p
    | subst1Term s (MInt i) = MInt i
    | subst1Term s (MAtom a) = subst1Atom s a

  and subst1Atom (v,t) (r as RVar v') =
      if vareq (v,v') then t else MAtom r
    | subst1Atom s (RApp (r,m)) =
      let val m' = subst1TermC s m
      in case subst1Atom s r
          of MAtom r' => MAtom (RApp (r', m'))
           | MLam (_, e) =>
             (* this is the hereditary subst1itution case. *)
             (subst1TermC (0,m') e)
           | _ => raise TypeError "impossible"
      end
    | subst1Atom s (RProj (d,r)) =
      (case subst1Atom s r
        of MAtom r' => MAtom (RProj (d,r'))
         | MPair p => proj d p
         | _ => raise TypeError "impossible")

  (* UNCOMMENT FOR SANITY CHECKING *)
  (* and subst1TermC s m = (checkSubst1Term s m; subst1Term s m) *)
  and subst1TermC s m = subst1Term s m


  (* converting exps to terms (ie. canonicalizing) *)
  (* canonicalize : exp -> term *)
  fun canonicalize (EInt i) = MInt i
    | canonicalize (ELam (t,e)) = MLam (t, canonicalize e)
    | canonicalize (EPair p) = on MPair canonicalize p
    | canonicalize (EVar v) = MAtom (RVar v)
    | canonicalize (EApp p) =
      (case both canonicalize p
        (* FIXME: calling subst1Term with a potentially open term! *)
        of (MLam (_, body), arg) => subst1Term (0,arg) body
         | (MAtom r, arg) => MAtom (RApp (r, arg))
         | _ => raise TypeError "impossible")
    | canonicalize (EProj (d,e)) =
      (case canonicalize e
        of MPair p => proj d p
         | MAtom r => MAtom (RProj (d,r))
         | _ => raise TypeError "impossible")


  (* simultaneous substitution *)
  type subst = int * term list

  fun liftSubst (i, ts) = (i+1, map liftTerm ts)

  (* This checks that we are substituting for all free vars of m that are >= i.
   *)
  fun checkSubstTerm (i, ts) m =
      (List.all (fn v => v < i + length ts) (termFV m)
       orelse raise TypeError "bad substitution";
      ())

  (* substLookup : subst -> var -> term option *)
  fun substLookup (n, ts) i =
      if i < n orelse i >= n + length ts then NONE
      else SOME (List.nth (ts, i - n))

  fun substTerm s (MAtom a) = substAtom s a
    | substTerm s (m as MInt _) = m
    | substTerm s (MPair p) = on MPair (substTermC s) p
    | substTerm s (MLam (tp,body)) =
      MLam (tp, substTermC (liftSubst s) body)

  and substAtom s (r as RVar v) = (case substLookup s v
                                    of SOME t => t
                                     | NONE => MAtom r)
    | substAtom s (RProj (d,a)) =
      (case substAtom s a
        of MPair p => proj d p
         | MAtom a' => MAtom (RProj (d,a'))
         | _ => raise TypeError "impossible")
    | substAtom s (RApp (a,m)) =
      let val m = substTermC s m
      in case substAtom s a
          of MLam (_, body) =>
             (* the hereditary substitution case *)
             substTermC (0,[m]) body
           | MAtom a => MAtom (RApp (a,m))
           | _ => raise TypeError "impossible"
      end

  (* UNCOMMENT FOR SANITY CHECKING *)
  (* and substTermC s m = (checkSubstTerm s m; substTerm s m) *)
  and substTermC s m = substTerm s m

  end                           (* local open Util in *)
end
