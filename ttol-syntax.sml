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

  (* substTpFor t n tau --> [t/n] tau *)
  fun substTpFor t v (e as TVar v') = (case Int.compare (v,v')
                                        of EQUAL => t
                                         | LESS => TVar (v'-1)
                                         | _ => e)
    | substTpFor t v (TUniv tau) = TUniv (substTpFor t (v+1) tau)
    | substTpFor t v (TArr ts) = on TArr (substTpFor t v) ts
    | substTpFor t v (TRec tau) = TRec (substTpFor t (v+1) tau)
    | substTpFor t v (TDown ifc) = TDown (ifcSubstTpFor t v ifc)
    | substTpFor _ _ (b as TBase _) = b

  and ifcSubstTpFor t v (IArr is) = on IArr (ifcSubstTpFor t v) is
    | ifcSubstTpFor t v (IProd is) = on IProd (ifcSubstTpFor t v) is
    | ifcSubstTpFor t v (IUp tau) = IUp (substTpFor t v tau)

  (* substTp t tau --> [t/0] tau *)
  fun substTp t = substTpFor t 0

  end                           (* local opens *)
end
