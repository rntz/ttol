structure TTOL = struct
  datatype proj = L | R
  fun proj L (x,_) = x
    | proj R (_,y) = y

  (* Both type, term, and library variables are DeBruijn indices. They are into
   * separate contexts, however, so eg 3 stands for different variables
   * depending on whether it is understood as a type, term, or library variable.
   *)
  type var = int

  (* interfaces *)
  datatype ifc = IArr of ifc * ifc
               | IProd of ifc * ifc
               | IUp of tp

  (* types *)
       and tp = TVar of var
              | TUniv of tp     (* binds type *)
              | TArr of tp * tp
              | TRec of tp      (* binds type *)
              | TDown of ifc
              | TBase of Base.tp

  (* expressions, parameterized over the types of canonical and atomic
   * libraries.
   *)
  datatype ('m,'r) exp
    = EVar of var
    | ELam of tp * ('m,'r) exp  (* binds exp *)
    | EApp of ('m,'r) exp * ('m,'r) exp
    | EPlam of ('m,'r) exp      (* binds typ *)
    | EPapp of ('m,'r) exp * tp
    | ERoll of tp * ('m,'r) exp (* binds type in tp *)
    | EUnroll of ('m,'r) exp
    (* library stuff *)
    | ELoad of ('m,'r) exp * ('m,'r) exp (* binds lib in exp2 *)
    | ELib of 'm
    | EUse of 'r
    (* base/prim stuff *)
    | EConst of Base.value
    | EPrim of Base.prim * ('m,'r) exp list

  (* libraries *)
  datatype lib = LVar of var
               | LLam of ifc * lib (* binds lib *)
               | LApp of lib * lib
               | LPair of lib * lib
               | LProj of proj * lib
               | LCode of expE  (* invariant: exp is value *)

  (* "external" expressions *)
  withtype expE = (lib, lib) exp

  (* canonical and atomic libraries *)
  datatype mlib = MAtom of rlib
                | MLam of ifc * mlib (* binds lib *)
                | MPair of mlib * mlib
                | MCode of expI

       and rlib = RVar of var
                | RApp of rlib * mlib
                | RProj of proj * rlib

  (* "internal" expressions *)
  withtype expI = (mlib, rlib) exp
end
