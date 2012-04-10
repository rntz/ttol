(* TODO: signature *)
structure Translate = struct
  local open Util
        open TTOL
        open Cam
  in

  datatype proj = datatype TTOL.proj
  val proj = TTOL.proj

  fun avar 0 = AVar
    | avar n = AShift (n, AVar)

  fun transExpOff off (e : expI) (rest : instr list) =
      let fun ins i = i :: rest
          fun inss is = is @ rest
          val trans = transExpOff off
      in case e
           of EVar v => ins (IAccess (off+v))
            | EApp (x,y) => trans x (trans y (ins IApply))
            | ELam (_,e) => ins (IClose (trans e [IRet]))
            | EPlam e => ins (IClose (transExpOff (off+1) e [IRet]))
            | EPapp (e,_) => trans e (inss [IConst (Base.VInt 0), (* dummy *)
                                            IApply])
            | ERoll (_,e) => trans e rest
            | EUnroll e => trans e rest
            | ELoad (e1,e2) => trans e1 (ILoad :: trans e2 rest)
            | ELib m => ins (ILib (transLib m))
            | EUse r => ins (IUse (transAtom r))
            | EConst c => ins (IConst c)
            | EPrim (p,es) =>
              (* foldr versus foldl important for arg. order *)
              foldr (uncurry trans) (ins (IPrim p)) es
      end

  and transLib (MAtom a) = LAtom (transAtom a)
    | transLib (MLam (_,m)) = LLam (transLib m)
    | transLib (MPair ms) = on LPair transLib ms
    | transLib (MCode e) =
      let fun f (EConst v) = CConst v
            | f (ELib m) = CLib (transLib m)
            | f (ELam (_,e)) = CFunc (transExpOff 0 e [IRet])
            | f (EPlam e) = CFunc (transExpOff 1 e [IRet])
            | f (ERoll (_,e)) = f e
            | f _ = raise Fail "code not a value"
      in LCode (f e)
      end

  and transAtom (RVar n) = avar n
    | transAtom (RApp (r,m)) = AApp (transAtom r, transLib m)
    | transAtom (RProj (d,r)) = AProj (d, transAtom r)


  val transExp = transExpOff 0
  fun transFunc e = transExp e [IRet]
  fun transProg p = transExp p []

  end                           (* local open Util in *)
end
