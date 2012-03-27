structure Base = struct
  (* should TypeError have args? *)
  exception TypeError

  datatype tp = TInt | TString
  fun tpEq (TInt, TInt) = true
    | tpEq (TString, TString) = true
    | tpEq _ = false

  datatype value = VInt of int
                 | VString of string

  (* valueType : value -> tp *)
  fun valueType (VInt _) = TInt
    | valueType (VString _) = TString

  (* primitive operations *)
  datatype arithop = OpAdd | OpSub | OpMul | OpDiv

  (* arithOpCall : arithop -> int * int -> int *)
  fun arithOpCall OpAdd : int * int -> int = op+
    | arithOpCall OpSub = op-
    | arithOpCall OpMul = op*
    | arithOpCall OpDiv = op div

  datatype prim = PArithop of arithop
                | PConcat
                | PPrint

  (* primType : prim -> (tp list * tp) *)
  fun primType (PArithop _) = ([TInt, TInt], TInt)
    | primType PConcat = ([TString, TString], TString)
    | primType PPrint = ([TString], TString)

  (* primCall : prim -> value list -> value
   * May have side effects.
   * May raise TypeError if called with ill-typed args.
   *)
  fun primCall PPrint [v as VString s] = v before print s
    | primCall PConcat [VString x, VString y] = VString (x ^ y)
    | primCall (PArithop oper) [VInt x, VInt y] = VInt (arithOpCall oper (x,y))
    | primCall _ _ = raise TypeError

end
