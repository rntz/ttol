(* signature SYNTAX = sig
 *  (* TODO *)
 * end *)

structure Syntax = struct
  local open Util
        open TTOL
        fun pairEq eq (x1,x2) (y1,y2) = eq (x1,y1) andalso eq (x2,y2)
  in

  exception Malformed

  fun tpEq (TVar v1, TVar v2) = v1 = v2
    | tpEq (TUniv t1, TUniv t2) = tpEq (t1, t2)
    | tpEq (TArr xs, TArr ys) = pairEq tpEq xs ys
    | tpEq (TRec t1, TRec t2) = tpEq (t1,t2)
    | tpEq (TDown i1, TDown i2) = ifcEq (i1,i2)
    | tpEq (TBase b1, TBase b2) = Base.tpEq (b1,b2)
    | tpEq _ = false

  and ifcEq (IArr xs, IArr ys) = pairEq ifcEq xs ys
    | ifcEq (IProd xs, IProd ys) = pairEq ifcEq xs ys
    | ifcEq (IUp t1, IUp t2) = tpEq (t1,t2)
    | ifcEq _ = false

  fun ifcMapTps f (IArr is) = on IArr (ifcMapTps f) is
    | ifcMapTps f (IProd is) = on IProd (ifcMapTps f) is
    | ifcMapTps f (IUp t) = IUp (f t)

  fun liftTpFromBy _ 0 t = t
    | liftTpFromBy from by t =
      let val recur = liftTpFromBy from by
      in case t
          of TVar v => TVar (if v >= from then v + by else v)
           | TUniv t => TUniv (liftTpFromBy (from+1) by t)
           | TArr ts => on TArr recur ts
           | TRec t => TRec (liftTpFromBy (from+1) by t)
           | TDown ifc => TDown (ifcMapTps recur ifc)
           | b as TBase _ => b
      end

  fun liftTp by t = liftTpFromBy 0 by t

  (* substTpFor t n tau --> [t/n] tau
   *
   * Precondition: t needs to be lifted by n.
   *)
  fun substTpFor t v (e as TVar v') = (case Int.compare (v,v')
                                        of EQUAL => liftTp v t
                                         | LESS => TVar (v'-1)
                                         | _ => e)
    | substTpFor t v (TUniv tau) = TUniv (substTpFor t (v+1) tau)
    | substTpFor t v (TArr ts) = on TArr (substTpFor t v) ts
    | substTpFor t v (TRec tau) = TRec (substTpFor t (v+1) tau)
    | substTpFor t v (TDown ifc) = TDown (ifcSubstTpFor t v ifc)
    | substTpFor _ _ (b as TBase _) = b

  and ifcSubstTpFor t v = ifcMapTps (substTpFor t v)

  (* substTp t tau --> [t/0] tau *)
  fun substTp t = substTpFor t 0


  (* Library variable substitution. *)
  (* The int is the number of library variable bindings passed over in the
   * interim (via ELoad).
   *)
  fun expMapLibUse (lib : int -> 'm1 -> 'm2)
                   (use : int -> 'r1 -> ('m2, 'r2) exp)
                   (e : ('m1,'r1) exp) : ('m2,'r2) exp =
      let fun f n (EVar v) = EVar v
            | f n (ELam (t,body)) = ELam (t, f n body)
            | f n (EApp es) = on EApp (f n) es
            | f n (EPlam e) = EPlam (f n e)
            | f n (EPapp (e,t)) = EPapp (f n e, t)
            | f n (ERoll (t, e)) = ERoll (t, f n e)
            | f n (EUnroll e) = EUnroll (f n e)
            | f n (ELoad (e1,e2)) = ELoad (f n e1, f (n+1) e2)
            | f n (ELib l) = ELib (lib n l)
            | f n (EUse r) = use n r
            | f _ (EConst c) = EConst c
            | f n (EPrim (p,es)) = EPrim (p, map (f n) es)
      in f 0 e
      end

  fun expMapLibs (mlib : int -> 'm1 -> 'm2)
                 (rlib : int -> 'r1 -> 'r2)
                 : ('m1,'r1) exp -> ('m2,'r2) exp =
      expMapLibUse mlib (fn i => EUse o rlib i)

  fun liftMlibFromBy _ 0 m = m
    | liftMlibFromBy from by m =
      let fun lift n = liftMlibFromBy (from+n) by
      in case m
          of MAtom r => MAtom (liftRlibFromBy from by r)
           | MLam (ifc,body) => MLam (ifc, lift 1 body)
           | MPair ms => on MPair (lift 0) ms
           | MCode e =>
             MCode (expMapLibs lift (fn i => liftRlibFromBy (from+i) by) e)
      end

  and liftRlibFromBy from by r =
      let val rrlib = liftRlibFromBy from by
      in case r
          of RVar v => RVar (if v >= from then v + by else v)
           | RApp (r,m) => RApp (rrlib r, liftMlibFromBy from by m)
           | RProj (p,r) => RProj (p, rrlib r)
      end

  fun liftMlib by m = liftMlibFromBy 0 by m

  (* mlibSubstLib M u N --> [M/u] N
   * rlibSubstLib M u R --> [M/u] R
   *  expSubstLib M u e --> [M/u] e
   *
   * Assumes that M needs to be lifted by u.
   *)
  fun mlibSubstLib M u (MAtom r) = rlibSubstLib M u r
    | mlibSubstLib M u (MLam (ifc, body)) =
      MLam (ifc, mlibSubstLib M (u+1) body)
    | mlibSubstLib M u (MPair ms) = on MPair (mlibSubstLib M u) ms
    | mlibSubstLib M u (MCode e) = MCode (expSubstLib M u e)

  and rlibSubstLib M u (r as RVar v) = (case Int.compare (u, v)
                                         of EQUAL => liftMlib u M
                                          | LESS => MAtom (RVar (v-1))
                                          | _ => MAtom r)
    | rlibSubstLib M u (RApp (r,m)) =
      let val m = mlibSubstLib M u m
      in case rlibSubstLib M u r
          of MAtom r => MAtom (RApp (r, m))
           | MLam (_, body) =>
             (* this is the hereditary substitution case *)
             mlibSubstLib m 0 body
           | _ => raise Malformed
      end
    | rlibSubstLib M u (RProj (p,r)) =
      (case rlibSubstLib M u r
        of MAtom r => MAtom (RProj (p,r))
         | MPair ms => proj p ms
         | _ => raise Malformed)

  and expSubstLib M u =
      expMapLibUse (fn i => mlibSubstLib M (u+i))
                   (fn i => fn r =>
                       case rlibSubstLib M (u+i) r
                        of MAtom r => EUse r
                         | MCode e => e
                         | _ => raise Malformed)


  local
    (* number of type, lib, and exp binders we are under *)
    type subcx = { subTps : int, subLibs : int, subExps : int }
    datatype sub = Tp of tp | Lib of mlib | Exp of expI
    val emptycx : subcx = { subTps = 0, subLibs = 0, subExps = 0 }

    fun underTp {subTps, subLibs, subExps} =
        {subTps = subTps + 1, subLibs = subLibs, subExps = subExps}
    fun underExp {subTps, subLibs, subExps} =
        {subTps = subTps, subLibs = subLibs, subExps = subExps + 1}
    fun underLib {subTps, subLibs, subExps} =
        {subTps = subTps, subLibs = subLibs + 1, subExps = subExps}

    fun varLifter by from which v = if v >= which from then v + which by else v

    fun tpLifter (by : subcx) (from : subcx) t =
        liftTpFromBy (#subTps from) (#subTps by) t

    fun ifcLifter (by : subcx) (from : subcx) = ifcMapTps (tpLifter by from)

    fun expLifter by from e =
        let val expLF = expLifter by
            val expL = expLF from
            val tpLF = tpLifter by
            val tpL = tpLF from
        in case e
            of EVar v => EVar (varLifter by from #subExps v)
             | ELam (t,e) => ELam (tpL t, expL e)
             | EApp es => on EApp expL es
             | EPlam e => EPlam (expLF (underTp from) e)
             | EPapp (e,t) => EPapp (expL e, tpL t)
             | ERoll (t,e) => ERoll (tpLF (underTp from) t, expL e)
             | EUnroll e => EUnroll (expL e)
             | ELoad (e1,e2) => ELoad (expL e1, expLF (underLib from) e2)
             | ELib m => ELib (libLifter by from m)
             | EUse r => EUse (atomLifter by from r)
             | e as EConst _ => e
             | EPrim (p,es) => EPrim (p, map expL es)
        end

    and libLifter by from m =
        let val libLF = libLifter by
            val libL = libLF from
        in case m
            of MAtom r => MAtom (atomLifter by from r)
             | MLam (ifc,body) => MLam (ifcLifter by from ifc,
                                        libLF (underLib from) body)
             | MPair ms => on MPair libL ms
             | MCode e => MCode (expLifter by from e)
        end

    and atomLifter by from r =
        let val atomL = atomLifter by from
        in case r
            of RVar v => RVar (varLifter by from #subLibs v)
             | RApp (r,m) => RApp (atomL r, libLifter by from m)
             | RProj (p,r) => RProj (p, atomL r)
        end

    fun expLift cx = expLifter cx emptycx
    fun libLift cx = libLifter cx emptycx

    fun tpSub (cx : subcx) (Tp t') t = substTpFor t' (#subTps cx) t
      | tpSub _ _ t = t

    fun ifcSub (cx : subcx) (Tp t) i = ifcSubstTpFor t (#subTps cx) i
      | ifcSub _ _ i = i

    fun varSub cx which lift mkvar v substitutee =
        case Int.compare (which cx, v)
         of EQUAL => lift cx substitutee
          | LESS => mkvar v
          | GREATER => mkvar (v - 1)

    fun expSub cx (Exp e) (EVar v) = varSub cx #subExps expLift EVar v e
      | expSub cx _ (e as EVar _) = e
      | expSub cx s (ELam (t,body)) = ELam (tpSub cx s t,
                                            expSub (underExp cx) s body)
      | expSub cx s (EApp es) = on EApp (expSub cx s) es
      | expSub cx s (EPlam e) = EPlam (expSub (underTp cx) s e)
      | expSub cx s (EPapp (e,t)) = EPapp (expSub cx s e, tpSub cx s t)
      | expSub cx s (ERoll (t,e)) = ERoll (tpSub (underTp cx) s t,
                                           expSub cx s e)
      | expSub cx s (EUnroll e) = EUnroll (expSub cx s e)
      | expSub cx s (ELoad (e1,e2)) = ELoad (expSub cx s e1,
                                             expSub (underLib cx) s e2)
      | expSub cx s (ELib m) = ELib (libSub cx s m)
      | expSub cx s (EUse r) = (case atomSub cx s r
                                 of MAtom r => EUse r
                                  | MCode e => e
                                  | _ => raise Malformed)
      | expSub _ _ (e as EConst _) = e
      | expSub cx s (EPrim (p,es)) = EPrim (p, map (expSub cx s) es)

    and libSub cx s (MAtom r) : mlib = atomSub cx s r
      | libSub cx s (MLam (ifc, body)) = MLam (ifcSub cx s ifc,
                                               libSub (underLib cx) s body)
      | libSub cx s (MPair ms) = on MPair (libSub cx s) ms
      | libSub cx s (MCode e) = MCode (expSub cx s e)

    and atomSub cx (Lib m) (RVar v) =
        varSub cx #subLibs libLift (MAtom o RVar) v m
      | atomSub cx _ (r as RVar _) = MAtom r
      | atomSub cx s (RApp (r,m)) =
        let val m = libSub cx s m
        in case atomSub cx s r
            of MAtom r => MAtom (RApp (r,m))
             | MLam (_, body) => libSub emptycx (Lib m) body
             | _ => raise Malformed
        end
      | atomSub cx s (RProj (p,r)) =
        (case atomSub cx s r
          of MAtom r => MAtom (RProj (p,r))
           | MPair ms => proj p ms
           | _ => raise Malformed)

  in

  end

  end                           (* local opens *)
end
