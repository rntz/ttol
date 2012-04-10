structure CAM = struct
  datatype proj = datatype TTOL.proj
  val proj = TTOL.proj

  datatype lib = LShift of int * lib
               | LAtom of atom
               | LPair of lib * lib
               | LLam of lib
               | LCode of code

       and atom = AVar of int
                | AApp of atom * lib
                | AProj of proj * atom

       and instr =
           (* -- CAM instrs -- *)
           IAccess of int       (* pushes nth env-val *)
         | IClose of code       (* pushes closure of code & current env *)
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
         | IFunc of code         (* pushes code w/ empty env *)

  withtype code = instr list

  type subst = lib list
  datatype value = VBase of Base.value
                 | VPrim of Base.prim
                 | VClos of code * env
                 | VLib of lib          (* nb. guaranteed closed *)
                 | VFrame of code * env (* return frame *)
  withtype env = value list * subst

  type state = { instrs : code, env : env, stack : value list }
  fun mkstate i e s : state = {instrs=i, env=e, stack=s}

  exception Stuck of string

  (* environment accessors *)
  val empty : env = ([],[])
  fun access n (vs, _) = List.nth (vs, n)
      handle Subscript => raise Stuck "variable out of bounds"

  fun addVal e (vs, ls) = (e::vs, ls)
  (* FIXME: probably wrong, need/want to lift ls? *)
  fun addLib l (vs, ls) = (vs, l::ls)

  (* substitution into libs *)
  fun evalLib (sub : subst) (l : lib) : lib = raise Fail "unimplemented"
  fun evalAtom (sub : subst) (a : atom) : lib = raise Fail "unimplemented"

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
           | ILib l => push (VLib (evalLib subst l))
           | IUse a => (case evalAtom subst a
                         of LCode c => push (VClos (c, empty))
                          | _ => raise Stuck "used atom did not eval to LCode")
           | ILoad => (case stack
                        of VLib l :: stack => mkstate is (addLib l env) stack
                         | _ => raise Stuck "invalid ILoad")
           | IFunc c => push (VClos (c, empty))
      end

end
