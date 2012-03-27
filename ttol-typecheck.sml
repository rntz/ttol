structure Typecheck : TYPECHECK = struct
  local open Util
        open TTOL
        open Syntax
  in

  exception TypeError

  (* tcx ::= ntyvars           (= Psi)                  "type context"
   * lcx ::= (tcx, libifcs)    (= Psi, Delta)           "lib context"
   * ecx ::= (lcx, exptys)     (= Psi, Delta, Gamma)    "exp context"
   *
   * ntyvars: # of tyvars bound
   * libifcs: list of library var interfaces
   * exptys: list of expression var types
   *)
  type tcx = int
  type lcx = tcx * ifc list
  type ecx = lcx * tp list

  val mkTcx : int -> tcx = id
  val mkLcx : int * ifc list -> lcx = id
  fun mkEcx (a,b,c) : ecx = (mkLcx (a,b), c)

  fun lcxEcx (lcx : lcx) : ecx = (lcx, [])

  val lcxTcx : lcx -> tcx = #1
  val ecxLcx : ecx -> lcx = #1
  val ecxTcx : ecx -> tcx = lcxTcx o ecxLcx

  val emptyTcx = mkTcx 0
  val emptyLcx = mkLcx (0, [])
  val emptyEcx = mkEcx (0, [], [])

  fun tcxOk (n : tcx) (v : var) = v <= n
  fun tcxAddTp n = n + 1

  fun lcxTpOk (tcx,_) v = tcxOk tcx v
  fun lcxIfc (cx as (tcx, ifcs) : lcx) (v : var) =
      List.nth (ifcs, v) handle Subscript => raise TypeError

  val lcxAddTp : lcx -> lcx = mapFst tcxAddTp
  fun lcxAddLib ifc (tcx, ifcs) = (tcx, ifc::ifcs)

  fun ecxTpOk (lcx,_) v = lcxTpOk lcx v
  fun ecxIfc (lcx,_) v = lcxIfc lcx v
  fun ecxTp (_,tps) v =
      List.nth (tps, v) handle Subscript => raise TypeError

  val ecxAddTp : ecx -> ecx = mapFst lcxAddTp
  (* val ecxAddLib : ifc -> ecx -> ecx = mapFst o lcxAddLib *)
  fun ecxAddLib ifc = mapFst (lcxAddLib ifc)
  fun ecxAddExp tp (lcx, tps) = (lcx, tp::tps)


  (* Type/interface well-formedness *)
  fun checkTp n (TVar v) = raiseUnless TypeError (tcxOk n v)
    | checkTp n (TUniv t) = checkTp (n+1) t
    | checkTp n (TArr ts) = on #1 (checkTp n) ts
    | checkTp n (TRec t) = checkTp (n+1) t
    | checkTp _ (TBase _) = ()
    | checkTp n (TDown i) = checkIfc n i

  and checkIfc n (IArr is) = on #1 (checkIfc n) is
    | checkIfc n (IProd is) = on #1 (checkIfc n) is
    | checkIfc n (IUp t) = checkTp n t

  fun inferIfc lcx t = (checkIfc (lcxTcx lcx) t; t)
  fun inferTp ecx t = (checkTp (ecxTcx ecx) t; t)

  (* Inference. *)
  fun inferExp (cx : ecx)
               (imlib : lcx -> 'm -> ifc)
               (irlib : lcx -> 'r -> ifc)
               (e : ('m,'r) exp) : tp =
      let fun infer cx = inferExp cx imlib irlib
          val recur = infer cx
          fun check tp e =
              raiseUnless TypeError (tpEq (tp, infer cx e))
      in case e
          of EVar v => ecxTp cx v
           | ELam (tp, body) =>
             TArr (inferTp cx tp, infer (ecxAddExp tp cx) body)
           | EApp (e1,e2) =>
             let val (t1,t2) = case recur e1 of TArr ts => ts
                                              | _ => raise TypeError
             in check t1 e2; t2
             end
           | EPlam body => TUniv (infer (ecxAddTp cx) body)
           | EPapp (e, tp) =>
             substTp (inferTp cx tp)
                     (case recur e of TUniv et => et
                                    | _ => raise TypeError)
           | ERoll (tpinner, e) =>
             let val tp = inferTp cx (TRec tpinner)
             in check (substTp tp tpinner) e; tp
             end
           | EUnroll e =>
             (case recur e of t as TRec tp => substTp t tp
                            | _ => raise TypeError)
           (* the library-related cases *)
           | ELoad (e1,e2) =>
             (case recur e1 of TDown i => infer (ecxAddLib i cx) e2
                             | _ => raise TypeError)
           | ELib mlib => TDown (imlib (ecxLcx cx) mlib)
           | EUse rlib =>
             (case irlib (ecxLcx cx) rlib of IUp t => t
                                           | _ => raise TypeError)
           (* base/prim cases *)
           | EConst c => TBase (Base.valueType c)
           | EPrim (p,es) =>
             let val (argtps, outtp) = Base.primType p
             in TBase outtp before
                ListPair.appEq (uncurry (check o TBase)) (argtps, es)
                handle UnequalLengths => raise TypeError
             end
      end

  (* inferring libs and exps containing them *)
  fun inferLib (cx : lcx) (l : lib) : ifc =
      let val recur = inferLib cx
      in case l
          of LVar v => lcxIfc cx v
           | LLam (ifc, body) =>
             IArr (inferIfc cx ifc,
                   inferLib (lcxAddLib ifc cx) body)
           | LApp (l1,l2) =>
             let val (i1,i2) = case recur l1 of IArr is => is
                                              | _ => raise TypeError
             in checkLib cx i1 l2; i2
             end
           | LPair ls => on IProd recur ls
           | LProj (p,l) =>
             (case recur l of IProd is => proj p is
                            | _ => raise TypeError)
           | LCode e => IUp (inferLExp (lcxEcx cx) e)
      end

  and inferLExp cx e = inferExp cx inferLib inferLib e

  and checkLib cx ifc l =
      raiseUnless TypeError (ifcEq (ifc, inferLib cx l))

  (* inferring mlibs, rlibs, and exps containing them *)
  fun inferMlib (cx : lcx) (l : mlib) : ifc =
      case l
       of MAtom r => inferRlib cx r
        | MLam (ifc, body) =>
          IArr (inferIfc cx ifc,
                inferMlib (lcxAddLib ifc cx) body)
        | MPair ms => on IProd (inferMlib cx) ms
        | MCode e => IUp (inferMRExp (lcxEcx cx) e)

  and checkMlib cx ifc l =
      raiseUnless TypeError (ifcEq (ifc, inferMlib cx l))

  and inferRlib (cx : lcx) (RVar v) : ifc = lcxIfc cx v
    | inferRlib cx (RApp (r,m)) =
      let val (i1,i2) = case inferRlib cx r of IArr is => is
                                             | _ => raise TypeError
      in checkMlib cx i1 m; i2
      end
    | inferRlib cx (RProj (p,r)) =
      (case inferRlib cx r of IProd is => proj p is
                            | _ => raise TypeError)

  and inferMRExp cx e = inferExp cx inferMlib inferRlib e

  end                           (* local opens *)
end
