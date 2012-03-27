signature IMPL = sig
  val canonLib : TTOL.lib -> TTOL.mlib
  val canonExp : TTOL.expE -> TTOL.expI

  exception Stuck
  val eval : TTOL.expI -> TTOL.expI
end

structure Impl : IMPL = struct
  local open Util
        open TTOL
        open Syntax
        open Typecheck
  in

  fun canonLib (LVar v) : mlib = MAtom (RVar v)
    | canonLib (LLam (ifc, body)) = MLam (ifc, canonLib body)
    | canonLib (LPair ls) = on MPair canonLib ls
    | canonLib (LApp ls) =
      (case both canonLib ls
        of (MLam (_, body), arg) => mlibSubstLib arg 0 body
         | (MAtom r, arg) => MAtom (RApp (r, arg))
         | _ => raise TypeError)
    | canonLib (LProj (p,l)) =
      (case canonLib l
        of MPair ls => proj p ls
         | MAtom r => MAtom (RProj (p,r))
         | _ => raise TypeError)
    | canonLib (LCode e) = MCode (canonExp e)

  and canonExp (EVar v : expE) : expI = EVar v
    | canonExp (ELam (tp,body)) = ELam (tp, canonExp body)
    | canonExp (EApp es) = on EApp canonExp es
    | canonExp (EPlam e) = EPlam (canonExp e)
    | canonExp (EPapp (e,t)) = EPapp (canonExp e, t)
    | canonExp (ERoll (t,e)) = ERoll (t, canonExp e)
    | canonExp (EUnroll e) = EUnroll (canonExp e)
    | canonExp (ELoad es) = on ELoad canonExp es
    | canonExp (ELib l) = ELib (canonLib l)
    | canonExp (EUse r) =
      (case canonLib r
        of MAtom r => EUse r
         | MCode e => e
         | _ => raise TypeError)
    | canonExp (EConst c) = EConst c
    | canonExp (EPrim (p,es)) = EPrim (p, map canonExp es)


  exception Stuck

  fun eval _ = raise Fail "unimplemented"

  end                           (* local opens *)
end
