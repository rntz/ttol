signature IMPL = sig
  exception Stuck

  val canonLib : TTOL.lib -> TTOL.mlib
  val canonExp : TTOL.expE -> TTOL.expI

  val eval : TTOL.expI -> TTOL.expI
end

structure Impl : IMPL = struct
  local open Util
        open TTOL
        open Syntax
        open Typecheck
  in

  exception Stuck

  fun canonLib (LVar v) : mlib = MAtom (RVar v)
    | canonLib (LLam (ifc, body)) = MLam (ifc, canonLib body)
    | canonLib (LPair ls) = on MPair canonLib ls
    | canonLib (LApp ls) =
      (case both canonLib ls
        of (MLam (_, body), arg) => mlibSubstLib arg 0 body
         | (MAtom r, arg) => MAtom (RApp (r, arg))
         | _ => raise Stuck)
    | canonLib (LProj (p,l)) =
      (case canonLib l
        of MPair ls => proj p ls
         | MAtom r => MAtom (RProj (p,r))
         | _ => raise Stuck)
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
         | _ => raise Stuck)
    | canonExp (EConst c) = EConst c
    | canonExp (EPrim (p,es)) = EPrim (p, map canonExp es)


  (* eval : expI -> expI *)
  fun eval (EVar _) = raise Stuck
    | eval (EApp (f,a)) =
      (case eval f of ELam (_,body) => expSubstExp (eval a) body
                    | _ => raise Stuck)
    | eval (EPapp (e,t)) =
      (case eval e of EPlam e' => eval (expSubstTp t e')
                    | _ => raise Stuck)
    | eval (ERoll (t,e)) = ERoll (t, eval e)
    | eval (EUnroll e) =
      (case eval e of ERoll (_,e) => e
                    | _ => raise Stuck)
    | eval (ELoad (e1,e2)) =
      (case eval e1 of ELib l => eval (expSubstLib l e2)
                     | _ => raise Stuck)
    | eval (EUse _) = raise Stuck
    (* primitive *)
    | eval (EPrim (p,es)) =
      let fun f e = case eval e of EConst c => c | _ => raise Stuck
      in EConst (Base.primCall p (map f es)
                 handle Base.TypeError => raise Stuck)
      end
    (* value cases *)
    | eval (e as ELam _) = e
    | eval (e as EPlam _) = e
    | eval (e as ELib _) = e
    | eval (e as EConst _) = e

  end                           (* local opens *)
end
