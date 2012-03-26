(* signature SYNTAX = sig
 *  (* TODO *)
 * end *)

structure Syntax = struct
  local open Util
        open TTOL
  in


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

  val emptyTcx = mkTcx 0
  val emptyLcx = mkLcx (0, [])
  val emptyEcx = mkEcx (0, [], [])

  fun checkTp n (TVar v) = if v <= n then () else raise TypeError
    | checkTp n (TUniv t) = checkTp (n+1) t
    | checkTp n (TArr ts) = on #1 (checkTp n) ts
    | checkTp n (TRec t) = checkTp (n+1) t
    | checkTp _ (TBase _) = ()
    | checkTp n (TDown i) = checkIfc n i

  and checkIfc n (IArr is) = on #1 (checkIfc n) is
    | checkIfc n (IProd is) = on #1 (checkIfc n) is
    | checkIfc n (IUp t) = checkTp n t

  end                           (* local opens *)
end
