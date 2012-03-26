(* signature SYNTAX = sig
 *  (* TODO *)
 * end *)

structure Syntax = struct
  local open Util
        open TTOL
        fun pairEq eq (x1,x2) (y1,y2) = eq (x1,y1) andalso eq (x2,y2)
  in

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

  end                           (* local opens *)
end


signature TYPECHECK = sig
  exception TypeError

  type tcx
  type lcx
  type ecx

  val mkTcx : int -> tcx
  val mkLcx : int * TTOL.ifc list -> lcx
  val mkEcx : int * TTOL.ifc list * TTOL.tp list -> ecx

  val emptyTcx : tcx
  val emptyLcx : lcx
  val emptyEcx : ecx

  val checkTp : tcx -> TTOL.tp -> unit
  val checkIfc : tcx -> TTOL.ifc -> unit
end

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
  fun ecxFrom (lcx : lcx) : ecx = (lcx, [])

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

  (* Inference. *)
  fun inferExp (cx : ecx)
               (imlib : lcx -> 'm -> ifc)
               (irlib : lcx -> 'r -> ifc)
               (e : ('m,'r) exp) : tp =
      raise Fail "unimplemented"

  fun inferLib (cx : lcx) (l : lib) : ifc =
      let val recur = inferLib cx
      in case l
          of LVar v => lcxIfc cx v
           | LLam (ifc, body) =>
             IArr (ifc, inferLib (lcxAddLib ifc cx) body)
           | LApp (l1,l2) =>
             let val (i1,i2) = case recur l1 of IArr is => is
                                              | _ => raise TypeError
             in checkLib cx i2 l2; i2
             end
           | LPair ls => on IProd recur ls
           | LProj (p,l) =>
             (case recur l of IProd is => proj p is
                            | _ => raise TypeError)
           | LCode e => IUp (inferExp (ecxFrom cx) inferLib inferLib e)
      end

  and checkLib cx ifc l =
      raiseUnless TypeError (ifcEq (ifc, inferLib cx l))

  end                           (* local opens *)
end
