(* Explicit substitutions *)
structure XSub = struct
  local open Util in

  type var = int

  (* isomorphic to (int * 'a list). *)
  infixr %
  datatype 'a subst = up of int
                    | % of 'a * 'a subst

  val sid : 'a subst = up 0

  (* UTLC *)
  datatype 'a view = Lam of 'a
                   | App of 'a * 'a
                   | Var of var

  end                           (* local open Util *)
end


structure XS = struct
  local open Util in

  open XSub
  infixr %
  infixr %@                     (* subst composition *)

  datatype exp = Exp of exp subst * exp view

  (* op%@ : exp subst * exp subst -> exp subst
   *
   * Think of s1 %@ s2 as "s1, then s2".
   *)
  fun s %@ (up 0) = s        (* useful optimization *)
    | (up 0) %@ s = s
    | (up k) %@ (up l) = up (k+l)
    | (up k) %@ (m % s) = up (k-1) %@ s
    | (m % s1) %@ s2 = subst s2 m % (s1 %@ s2)

  and subst s2 (Exp (s1, e)) = Exp (s1 %@ s2, e)

  (* hide : exp view -> exp *)
  fun hide e = Exp (sid, e)
  val hvar = hide o Var
  val hlam = hide o Lam
  val happ = curry (hide o App)

  (* lookup : (exp -> exp view) -> exp subst -> var -> exp view
   *
   * An odd function, but useful.
   *)
  fun lookup f (up k) i = Var (i+k)
    | lookup f (e % _) 0 = f e
    | lookup f (_ % s) i = lookup f s (i-1)

  (* show : exp -> exp view *)
  fun show (Exp (s, e)) =
      (* XXX this case is a hack. shouldn't be useful/necessary, but is. *)
      case s of up 0 => e | _ =>
      case e of Var v => lookup show s v
              | App p => on App (subst s) p
              | Lam e => Lam (subst (hvar 0 % (s %@ up 1)) e)

  (* Evaluation. *)
  datatype stuck = Unbound of var
                 | NotLam of exp view
  exception Stuck of stuck
  fun getLam (Lam e) = e
    | getLam e = raise Stuck (NotLam e)

  (* A direct definition of eval. *)
  fun eval e =
      case show e
       of Var i => raise Stuck (Unbound i)
        | App (f,a) =>
          let val body = getLam (show (eval f))
          in (* we get call-by-name semantics if here we do instead:
              *   eval (subst (a % sid) body)
              *)
              eval (subst (eval a % sid) body)
          end
        | e as Lam _ => hide e

  (* evalSub : exp subst -> exp -> exp view
   * evalSubView : exp subst -> exp view -> exp view
   *
   * A definition which avoids calling subst, to show that consing up new Exps
   * is unnecessary, and make clearer the correspondence with
   * environment-carrying eval implementations.
   *)
  fun evalSub s1 (Exp (s2,e)) = evalSubView (s2 %@ s1) e

  and evalSubView s (Var v) : exp view =
      lookup (fn (Exp (s,e)) => evalSubView s e) s v
    | evalSubView s (App (f,a)) =
      let val body = getLam (evalSub s f)
      in (* XXX not sure this is correct *)
         (* we get call-by-name semantics if here instead we do:
          *   evalSub (a % s) body
          *)
          evalSub (hide (evalSub s a) % s) body
      end
    (* this call to Exp is annoying. is there a way around it? *)
    | evalSubView s (e as Lam _) = show (Exp (s, e))

  end                           (* local open Util in *)
end


structure XS2 = struct
  local open Util in

  open XSub
  infixr %
  infixr %@                     (* subst composition *)

  (* We only allow substitutions at outermost level. *)
  datatype term = Term of term view
  datatype exp = Exp of exp subst * term

  fun unroll (Term t) = t
  fun exp t = Exp (sid, t)
  val tvar = Term o Var
  val tlam = Term o Lam
  val tapp = curry (Term o App)

  fun evar i = Exp (sid, tvar i)

  (* op%@ : exp subst * exp subst -> exp subst
   *
   * Think of s1 %@ s2 as "s1, then s2".
   *)
  fun s %@ (up 0) = s        (* useful optimization *)
    (* TODO: check how often this^ branch is actually taken *)
    | (up 0) %@ s = s
    | (up k) %@ (up l) = up (k+l)
    | (up k) %@ (m % s) = up (k-1) %@ s
    | (m % s1) %@ s2 = subst s2 m % (s1 %@ s2)

  and subst s2 (Exp (s1, t)) = Exp (s1 %@ s2, t)

  (* lookup : (var -> 'a) -> (exp -> 'a) -> exp subst -> var -> 'a
   *
   * An odd function, but useful.
   *)
  fun lookup v _ (up k) i = v (i+k)
    | lookup _ f (e % _) 0 = f e
    | lookup v f (_ % s) i = lookup v f s (i-1)

  (* show : exp -> exp view *)
  fun show (Exp (s, Term t)) =
      case t of Var v => lookup Var show s v
              | App p => on App (curry Exp s) p
              | Lam t => Lam (Exp (evar 0 % (s %@ up 1), t))

  (* Evaluation *)
  datatype stuck = Unbound of var
                 | NotLam of term view
  exception Stuck of stuck

  (* eval : exp -> exp
   *
   * NB. assumes things in substitution are already evalled.
   *)
  fun eval (e as Exp (s, Term t)) : exp =
      case t
       of Lam _ => e            (* done. *)
        | Var i =>
          (* not sure this will use the correct env for evaluating the thing
           * looked up. Do we want (evalS s) instead? *)
          (* a hacked version of lookup *)
          lookup (fn i => raise Stuck (Unbound i)) eval s i
        | App (f,a) =>
          (case eval (Exp (s, f))
            of Exp (fsub, Term (Lam fbody)) =>
               let val ae = eval (Exp (s, a))
               in eval (Exp (ae % (fsub %@ up 1), fbody))
               end
             | Exp (_, Term t) => raise Stuck (NotLam t))

  (* fun eval e =
   *     case show e
   *      of Var i => raise Stuck (Unbound i)
   *       | App (f,a) =>
   *         (case eval f
   *           of Exp (fsub, Term (Lam fbody)) =>
   *              let val ae = eval a
   *              in eval (Exp (ae % (fsub %@ up 1), fbody))
   *              end
   *            | Exp (_, Term t) => raise Stuck (NotLam t)) *)

  end                           (* local open Util in *)
end
