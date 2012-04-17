structure T = struct
  open TTOL

  fun eint x = EConst (Base.VInt x)

  (* Test of Syntax. Demonstrates breakage. *)
  val mlib_foo = MLam (IUp (TBase Base.TInt),
                       MPair (MAtom (RVar 0), MAtom (RVar 7)))
  val anexp : expI =
      ELib (MAtom (RApp (RVar 0, MAtom (RVar 1))))

  val anexpres = Syntax.expSubstLib mlib_foo anexp

  (* Direct test of CAM. *)
  open Cam

  fun fsquare i = [i, IAccess 0, IApply, IAccess 0, IApply, IRet]

  val fmul = [IClose [IAccess 1, IAccess 0,
                      IPrim (Base.PArithop Base.OpMul), IRet],
              IRet]

  fun avar 0 = AVar
    | avar n = AShift (n, AVar)

  val lmul = LCode (CFunc fmul)
  val lsquare = LLam (LCode (CFunc (fsquare (IUse AVar))))
  val llink = LAtom (AApp (avar 0, LAtom (avar 1)))

  val prog = [ILib lsquare,
              ILib lmul,
              ILoad,            (* lib push lmul; 0=lmul *)
              ILoad,            (* lib push lsquare; 0=lsquare, 1=lmul *)
              ILib llink,       (* val push llink *)
              ILoad,            (* lib push llink; 0=llink, 1=lsquare, 2=lmul *)
              IUse (avar 0),    (* val push (contents llink) *)
              IConst (Base.VInt 7),
              IApply
             ]

  (* Test for substitution. *)
  val lib_foo = LLam (LPair (LAtom (AVar), LAtom (avar 7)))
  val ablock = [ ILib (LAtom (AApp (avar 0, LAtom (avar 1)))) ]
  val ablockres = substBlock (0, [lib_foo]) ablock

  (* Test of translation. *)
  val tint = TBase Base.TInt
  val pmul = Base.PArithop Base.OpMul

  val emul : expI = ELam (tint, ELam (tint, EPrim (pmul, [EVar 1, EVar 0])))
  val esquare : expI = ELam (tint, EApp (EApp (EUse (RVar 0), EVar 0), EVar 0))

  val mmul = MCode emul
  val msquare = MLam (IUp (TArr (tint, TArr (tint, tint))),
                      MCode esquare)
  val mlink = MAtom (RApp (RVar 0, MAtom (RVar 1)))

  val iprog = ELoad (ELib mmul,
               ELoad (ELib msquare,
                ELoad (ELib mlink,
                 EApp (EUse (RVar 0), EConst (Base.VInt 7)))))

  val tprog = Translate.transProg iprog

end
