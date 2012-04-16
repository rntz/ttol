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

  val inferLib : lcx -> TTOL.lib -> TTOL.ifc
  val inferMlib : lcx -> TTOL.mlib -> TTOL.ifc
  val inferRlib : lcx -> TTOL.rlib -> TTOL.ifc

  val inferExp : ecx ->
                 (lcx -> 'm -> TTOL.ifc) ->
                 (lcx -> 'r -> TTOL.ifc) ->
                 ('m,'r) TTOL.exp ->
                 TTOL.tp

  val inferLExp : ecx -> (TTOL.lib, TTOL.lib) TTOL.exp -> TTOL.tp
  val inferMRExp : ecx -> (TTOL.mlib, TTOL.rlib) TTOL.exp -> TTOL.tp

end
