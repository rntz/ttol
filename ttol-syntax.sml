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

  fun substTp (t : tp) (into : tp) : tp =
      raise Fail "unimplemented"

  end                           (* local opens *)
end
