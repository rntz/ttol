(* TODO: signature *)
structure Cam = struct
  local open Util in

  datatype proj = datatype TTOL.proj
  val proj = TTOL.proj

  datatype lib = LShift of int * lib
               | LAtom of atom
               | LPair of lib * lib
               | LLam of lib
               | LCode of code

       and atom = AVar          (* no need for int, have AShift *)
                | AApp of atom * lib
                | AProj of proj * atom
                | AShift of int * atom

       and instr =
           (* -- CAM instrs -- *)
           IAccess of int       (* pushes nth env-val *)
         | IClose of block      (* pushes closure w/ current env *)
           (* pops arg, closure; pushes ret frame;
            * jumps to closure w/env extended w/ arg *)
         | IApply
           (* pos value & ret frame, pushes value, jumps to ret frame *)
           (* NB. could just take "end of instr sequence" as ret,
            * but this makes it more explicit. *)
         | IRet
         (* -- New instructions -- *)
         | IConst of Base.value  (* pushes value *)
         | IPrim of Base.prim    (* pushes prim *)
         | ILib of lib           (* pushes eval of lib in curr. lib subst *)
         | IUse of atom          (* pushes eval of atom in curr. lib subst *)
         | ILoad                 (* moves top of stack into lib. subst *)
         (* pushes closure w/ empty env.
          * int is a shift; used to avoid copying during lib. subst.
          *)
         | IFunc of int * block

       and code = CFunc of block
                | CLib of lib
                | CConst of Base.value
                | CPrim of Base.prim

  withtype block = instr list

  type subst = int * lib list   (* int is terminating shift *)
  datatype value = VBase of Base.value
                 | VPrim of Base.prim
                 | VClos of block * env
                 | VLib of lib           (* nb. guaranteed closed *)
                 | VFrame of block * env (* return frame *)
  withtype env = value list * subst


  type state = { instrs : instr list, env : env, stack : value list }
  fun mkstate i e s : state = {instrs=i, env=e, stack=s}

  exception Stuck of string

  (* substitution manipulation. *)
  val idsubst = (0,[])

  (* Shifting and unshifting. *)
  fun shiftL 0 l = l
    | shiftL n (LShift (m,l)) = LShift (n+m,l)
    | shiftL n l = LShift (n, l)

  fun unshiftL (LShift (k,l)) =
      (k, case l of LShift _ => raise Stuck "nested LShifts" | _ => l)
    | unshiftL l = (0, l)

  fun shiftA 0 a = a
    | shiftA n (AShift (m,a)) = AShift (n+m, a)
    | shiftA n a = AShift (n,a)

  (* first arg is shift. *)
  fun codeInstr k (CFunc f) = IFunc (k, f)
    | codeInstr k (CLib l) = ILib (shiftL k l)
    | codeInstr _ (CConst c) = IConst c
    | codeInstr _ (CPrim p) = IPrim p

  (* TODO: optimization: cons (LAtom (AShift (n, AVar))) (n+1, []) = (n, []).
   * check whether it helps before committing to this optimization.
   *)
  fun cons (l : lib) ((n,s) : subst) : subst = (n, l::s)

  (* (^k o s) in explicit substitution notation *)
  fun drop 0 s : subst = s
    | drop k (n,[]) = (n+k,[])
    | drop k (n, _::xs) = drop (k-1) (n,xs)

  (* (s o ^k) in explicit substitution notation *)
  fun shift 0 s = s
    | shift k (n,ls) = (k+n, map (shiftL k) ls)

  (* The following definition corresponds more exactly with definition of
   * composition of substitutions:
   *
   * fun shift 0 s : subst = s
   *   | shift k (n,[]) = (k+n,[])
   *   | shift k (n, l::ls) = cons (shiftL k l) (shift k (n,ls))
   *)

  (* (M . (s o ^1)) in explicit substitution notation *)
  fun bindLib l s = cons l (shift 1 s)

  (* puts a substitution under a binder
   * (0 . (s o ^1)) in explicit substitution notation *)
  fun bind s = bindLib (LAtom AVar) s

  (* substitution *)
  (* TODO: optimize this by returning an option, w/ NONE for "no changes".
   * (improves sharing.) *)
  fun substLib ((0,[]) : subst) (l : lib) : lib = l
    | substLib (n,[]) (LShift (m,l)) = LShift (n+m, l)
    | substLib (n,[]) l = LShift (n,l)
    | substLib s (LShift (k,l)) = substLib (drop k s) l
    | substLib s (LPair ls) = on LPair (substLib s) ls
    | substLib s (LLam e) = LLam (substLib (bind s) e)
    | substLib s (LCode c) = LCode (substCode s c)
    | substLib s (LAtom a) = substAtom s a

  (* TODO: ^ same optimization. *)
  (* invariant: given an atom of type t, unshiftL (substAtom s a) is either:
   * - (k, LAtom a)
   * - (k, l) where l is an introduction for type t
   *)
  and substAtom ((n,[]) : subst) (a : atom) = LAtom (shiftA n a)
    | substAtom s (AShift (k,a)) = substAtom (drop k s) a
    | substAtom (_, l::_) AVar = l
    | substAtom s (AApp (a,l)) =
      let val l = substLib s l
      in case unshiftL (substAtom s a)
          of (k, LAtom a) => LAtom (AApp (shiftA k a, l))
           | (k, LLam body) =>
             (* hereditary substitution case *)
             substLib (k,[l]) body
           | _ => raise Stuck "subst into AApp did not yield lambda or atom"
      end
    | substAtom s (AProj (d,a)) =
      (case unshiftL (substAtom s a)
        of (k, LAtom a) => LShift (k, LAtom (AProj (d,a)))
         | (k, LPair ls) => shiftL k (proj d ls)
         | _ => raise Stuck "subst into AProj did not yield pair or atom")

  and substCode (s : subst) (CFunc f) = CFunc (substBlock s f)
    | substCode s (CLib l) = CLib (substLib s l)
    | substCode _ (c as CConst _) = c
    | substCode _ (p as CPrim _) = p

  and substBlock _ [] = []
    | substBlock s (ILoad::is) = ILoad :: substBlock (bind s) is
    | substBlock s (i::is) = substInstr s i :: substBlock s is

  and substInstr s (ILib l) = ILib (substLib s l)
    | substInstr s (IUse a) =
      (case unshiftL (substAtom s a)
        of (k, LAtom a) => IUse (shiftA k a)
         | (k, LCode c) => codeInstr k c
         | _ => raise Stuck "bad substitution into IUse")
    | substInstr s (IClose f) = IClose (substBlock s f)
    (* are funcs guaranteed closed? Not during lib substitution!
     * only once all libs have been subbed in are they closed.
     *)
    | substInstr s (IFunc (k,is)) =
      IFunc (case drop k s
              of (k,[]) => (k,is)
               (* TODO: is there something smart we can do here? *)
               | s => (0, substBlock s is))
    | substInstr _ ILoad = raise Fail "impossible"
    | substInstr _ i = i


  (* environment manipulation *)
  val empty : env = ([], idsubst)
  fun access n (vs, _) = List.nth (vs, n)
      handle Subscript => raise Stuck "variable out of bounds"

  fun addVal e (vs, ls) = (e::vs, ls)
  fun addLib l (vs, ls) = (vs, bindLib l ls)
  (* the more obvious "fun addLib l (vs,ls) = (vs, cons l ls)"
   * works, but increases copying. TODO: explain.
   *)

  fun codeVal (CFunc f) = VClos (f, empty)
    | codeVal (CLib l) = VLib l
    | codeVal (CConst c) = VBase c
    | codeVal (CPrim p) = VPrim p

  (* step : state -> state *)
  fun step (s as {instrs, env, stack} : state) : state =
      let val (i, is) = case instrs of i::is => (i,is)
                                     | [] => raise Stuck "no instrs"
          val subst = #2 env
          fun push (x : value) = mkstate is env (x::stack)
      in case i
          of IAccess n => push (access n env)
           | IClose c => push (VClos (c,env))
           | IApply => (case stack
                         of arg::VClos(c,e)::stk => mkstate c (addVal arg e) stk
                          | _ => raise Stuck "invalid IApply")
           | IRet => (List.null is orelse raise Stuck "excess instrs after ret";
                     case stack
                      of ret::VFrame(c,e)::stk => mkstate c e (ret::stk)
                       | _ => raise Stuck "invalid IRet")
           | IConst v => push (VBase v)
           | IPrim p => push (VPrim p)
           | ILib l => push (VLib (substLib subst l))
           | IUse a => (case unshiftL (substAtom subst a)
                         of (k, LCode c) =>
                            (* c must be closed, so we can ignore k.
                             * TODO: is there an invariant about k we can check?
                             * should it be 0?
                             *)
                            push (codeVal c)
                          | _ => raise Stuck "used atom did not subst to LCode")
           | ILoad => (case stack
                        of VLib l :: stack => mkstate is (addLib l env) stack
                         | _ => raise Stuck "invalid ILoad")
           (* TODO: I think shift amount should correspond to size of subst?
            * check this.
            *)
           | IFunc (_,c) => push (VClos (c, empty))
      end

  end                           (* local open Util in *)
end
