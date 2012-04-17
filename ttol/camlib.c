/* slz is a serialization library. see http://github.com/rntz/slz */
#include "camlib.h"

#include <gc.h>
#include <slz.h>

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#define NEW(typ) GC_MALLOC(sizeof(typ))

#define DEOFFSET(typ, mem, ptr) ((typ*)(((char*)(ptr)) - offsetof(typ, mem)))


/* Reading things from bytecode stream. */
#define NEXT(ipp) *((*(ipp))++)

/* NB.We read big-endian. */
#define READIN(ipp, dest) do {                          \
        dest = 0;                                       \
        for (size_t _readnbytes_index = 0;              \
             _readnbytes_index < sizeof(dest);          \
             ++_readnbytes_index) {                     \
            dest = (dest << CHAR_BIT) + NEXT(ipp);      \
        }                                               \
    } while (0)

#define READER(name)                            \
    name##_t read_##name(ip_t *ipp) {           \
        name##_t val;                           \
        READIN(ipp, val);                       \
        return val;                             \
    }

op_t read_op(ip_t *ipp) { return NEXT(ipp); }

READER(shift)
READER(int)
READER(uintptr)

lib_t  *read_lib(ip_t *ipp) { return (lib_t*) read_uintptr(ipp); }
atom_t *read_atom(ip_t *ipp) { return (atom_t*) read_uintptr(ipp); }
ip_t    read_block(ip_t *ipp) { return (ip_t) read_uintptr(ipp); }
char   *read_string(ip_t *ipp) { return (char*) read_uintptr(ipp); }


/* Environment & stack manipulation. */
void env_access(env_t *env, shift_t idx, val_t *out) {
    valenv_t *node = env->valenv;
    while (idx--) {
        assert (node);
        node = node->next;
    }
    assert (node);
    *out = node->val;
}

void env_push(env_t *env, val_t val) {
    valenv_t *node = NEW(valenv_t);
    node->next = env->valenv;
    node->val = val;
    env->valenv = node;
}

bool stack_empty(stack_t *stack) {
    assert (stack->sp >= stack->start);
    return stack->sp == stack->start;
}

val_t stack_pop(stack_t *stack) {
    assert (!stack_empty(stack));
    val_t res = *--stack->sp;
    /* zero it so as not to keep object around. */
    memset(stack->sp, 0, sizeof(val_t));
    return res;
}

val_t *stack_push(stack_t *stack) {
    size_t idx = (size_t)(stack->sp - stack->start);
    if (idx == stack->size) {
        stack->size *= 2;
        stack->start = GC_REALLOC(stack->start, stack->size * sizeof(val_t));
        stack->sp = stack->start + idx;
    }
    assert ((size_t)(stack->sp - stack->start) < stack->size);
    return stack->sp++;
}

int_t stack_pop_int(stack_t *stack) {
    val_t v = stack_pop(stack);
    assert (v.tag == VAL_INT);
    return v.data.num;
}

void stack_push_int(stack_t *stack, int_t val) {
    val_t *p = stack_push(stack);
    p->tag = VAL_INT;
    p->data.num = val;
}

void stack_push_closure(stack_t *stack, ip_t block, env_t env) {
    closure_t *clos = NEW(closure_t);
    clos->block = block;
    clos->env = env;
    val_t *slot = stack_push(stack);
    slot->tag = VAL_CLOSURE;
    slot->data.closure = clos;
}


/* Library manipulation */
lib_t *shift_lib(lib_t *lib, shift_t shift) {
    lib_shift_t *l = NEW(lib_shift_t);
    l->link.tag = LIB_SHIFT;
    l->shift = shift;
    if (lib->tag != LIB_SHIFT)
        l->inner = lib;
    else {
        lib_shift_t *l2 = DEOFFSET(lib_shift_t, link, lib);
        l->shift += l2->shift;
        l->inner = l2->inner;
    }
    assert (l->inner->tag != LIB_SHIFT);
    return &l->link;
}

lib_t *unshift_lib(lib_t *lib, shift_t *out) {
    if (lib->tag == LIB_SHIFT) {
        lib_shift_t *l = DEOFFSET(lib_shift_t, link, lib);
        *out = l->shift;
        assert (l->inner->tag != LIB_SHIFT && "no nested lib_shifts");
        return l->inner;
    }
    *out = 0;
    return lib;
}

atom_t *shift_atom(atom_t *atom, shift_t shift) {
    atom_shift_t *a = NEW(atom_shift_t);
    a->link.tag = ATOM_SHIFT;
    a->shift = shift;
    if (atom->tag != ATOM_SHIFT)
        a->inner = atom;
    else {
        atom_shift_t *a2 = DEOFFSET(atom_shift_t, link, atom);
        a->shift += a2->shift;
        a->inner = a2->inner;
    }
    assert (a->inner->tag != ATOM_SHIFT);
    return &a->link;
}


/* Substitution manipulation */
shift_t subst_get_shift(subst_t *subst) {
    assert (subst->tag == SUBST_SHIFT);
    return DEOFFSET(subst_shift_t, link, subst)->shift;
}

lib_t *subst_get_lib(subst_t *subst) {
    assert (subst->tag == SUBST_LIB);
    return DEOFFSET(subst_lib_t, link, subst)->lib;
}

bool subst_lookup(subst_t *subst, shift_t var, atom_t **atomp, lib_t **libp) {
    shift_t accum = 0;
    for (;;) {
        /* Is this correct? */
        while (subst && (subst->tag == SUBST_SHIFT)) {
            accum += DEOFFSET(subst_shift_t, link, subst)->shift;
            subst = subst->next;
        }

        if (!var || !subst)
            break;
        --var, ++accum, subst = subst->next;
    }

    if (!subst) {
        /* Ran off end of substitution (hit terminating "id"). */
        atom_var_t *v = NEW(atom_var_t);
        v->link.tag = ATOM_VAR;
        v->var = var + accum;
        *atomp = &v->link;
        return false;
    }

    switch (subst->tag) {
      case SUBST_LIB:
        *libp = shift_lib(DEOFFSET(subst_lib_t, link, subst)->lib, accum);
        return true;

      case SUBST_VAR: {
          atom_var_t *v = NEW(atom_var_t);
          v->link.tag = ATOM_VAR;
          v->var = accum;
          *atomp = &v->link;
          return false;
      }

      case SUBST_SHIFT:
        assert(0 && "impossible");
    }
    assert (0 && "unrecognized subst tag");
}

void subst_shift(subst_shift_t *s, shift_t shift, subst_t *orig) {
    assert (shift);

    shift_t accum = shift;
    shift_t i = shift;
    while (orig && i--) {
        if (orig->tag == SUBST_SHIFT)
            accum += subst_get_shift(orig);
        orig = orig->next;
    }

    s->link.tag = SUBST_SHIFT;
    s->link.next = orig;
    s->shift = accum;
}

/* useful for null-checking. */
#define OR(x,y) ((x) ? (x) : (y))

/* returns true and sets libp if result is library. (guaranteed not to be a
 * library wrapping an atom, even with an intevening shift.)
 *
 * returns false and sets atomp if result is atom. sets atomp to NULL if result
 * atom is same as input.
 */
bool atom_subst(subst_t *subst, atom_t *atom, atom_t **atomp, lib_t **libp) {
    if (!atom_subst_fast(subst, atom, atomp, libp))
        return false;

    shift_t shift;
    lib_t *l = unshift_lib(*libp, &shift);
    if (l->tag != LIB_ATOM)
        return true;

    /* Was a wrapped atom. Return it directly. */
    *atomp = shift_atom(DEOFFSET(lib_atom_t, link, l)->atom, shift);
    return false;
}

lib_t *atom_subst_lib(subst_t *subst, atom_t *atom) {
    lib_t *r;
    if (atom_subst_fast(subst, atom, &atom, &r))
        return r;
    if (!atom)
        return NULL;
    lib_atom_t *l = NEW(lib_atom_t);
    l->link.tag = LIB_ATOM;
    l->atom = atom;
    return &l->link;
}

/* returns true and sets libp if result is library. (might be a library wrapping
 * an atom.)
 *
 * returns false and sets atomp if result is atom. sets atomp to NULL if result
 * atom is same as input.
 */
bool atom_subst_fast(subst_t *subst, atom_t *atom, atom_t **atomp, lib_t **libp)
{
    switch (atom->tag) {
      case ATOM_VAR:
        return subst_lookup(subst, DEOFFSET(atom_var_t, link, atom)->var,
                            atomp, libp);

      case ATOM_SHIFT: {
          atom_shift_t *a = DEOFFSET(atom_shift_t, link, atom);
          assert (a->shift && "should never have shift by 0");
          assert (a->inner->tag != ATOM_VAR &&
                  "should never have atom_var inside atom_shift");

          subst_shift_t ss;
          subst_shift(&ss, a->shift, subst);
          if (!ss.link.next) {
              if (ss.shift == a->shift) {
                  /* I think this should never happen. */
                  assert (0 && "impossible");
                  /* But if it does, here's how to handle it. */
                  *atomp = NULL;
                  return false;
              }

              /* We're just doing a shift. */
              *atomp = shift_atom(a->inner, ss.shift);
              return false;
          }

          return atom_subst_fast(&ss.link, a->inner, atomp, libp);
      }

      case ATOM_PROJ: {
          atom_proj_t *proj = DEOFFSET(atom_proj_t, link, atom);
          lib_t *lib;
          if (!atom_subst(subst, proj->inner, &atom, &lib)) {
              if (!atom)
                  *atomp = NULL;
              else {
                  atom_proj_t *r = NEW(atom_proj_t);
                  r->link.tag = ATOM_PROJ;
                  r->dir = proj->dir;
                  r->inner = atom;
                  *atomp = &r->link;
              }
              return false;
          }

          /* inner evaluated to canonical form, in lib */
          shift_t shift;
          lib = unshift_lib(lib, &shift);
          assert (lib->tag == LIB_PAIR);
          *libp = DEOFFSET(lib_pair_t, link, lib)->libs[proj->dir];
          return true;
      }

      case ATOM_APP: {
          atom_app_t *app = DEOFFSET(atom_app_t, link, atom);
          atom_t *funcatom;
          lib_t *funclib, *arg = lib_subst(subst, app->arg);

          if (!atom_subst(subst, app->func, &funcatom, &funclib)) {
              if (!funcatom && !arg)
                  *atomp = NULL;
              else {
                  atom_app_t *r = NEW(atom_app_t);
                  r->link.tag = ATOM_APP;
                  r->func = OR(funcatom, app->func);
                  r->arg = OR(arg, app->arg);
                  *atomp = &r->link;
              }
              return false;
          }

          /* func evaluated to canonical form, in funclib */
          shift_t shift;
          funclib = unshift_lib(funclib, &shift);
          assert (funclib->tag == LIB_LAMBDA);

          /* `shift - 1' can result in a "negative" shift. This is OK because we
           * are inside a subst_lib_t, so we'll only reach this node if our
           * shift is >= 1. The reason for the - 1 is that the desired
           * corresponding explicit substitution is [L . ^shift], and without
           * the - 1 we'd get [L . ^(shift+1)].
           */
          subst_shift_t sshift = {
              .link = { .tag = SUBST_SHIFT, .next = NULL },
              .shift = shift - 1 };
          subst_lib_t slib = {
              .link = { .tag = SUBST_LIB, .next = &sshift.link },
              .lib = OR(arg, app->arg) };

          lib_t *body = DEOFFSET(lib_lambda_t, link, funclib)->body;
          *libp = lib_subst(&slib.link, body);
          if (!*libp)
              *libp = body;
          return true;
      }
    }

    (void) subst, (void) atom, (void) atomp, (void) libp;
    assert (0 && "unrecognized atom tag");
}

/* returns NULL if no copy was necessary. */
lib_t *lib_subst(subst_t *subst, lib_t *lib) {
    assert (subst);

    switch (lib->tag) {
      case LIB_ATOM:
        return atom_subst_lib(subst, DEOFFSET(lib_atom_t, link, lib)->atom);

      case LIB_PAIR: {
          lib_t **libs = DEOFFSET(lib_pair_t, link, lib)->libs;
          lib_t *left = lib_subst(subst, libs[0]),
                *right = lib_subst(subst, libs[1]);
          if (!left && !right)
              return NULL;

          /* Make new pair. */
          lib_pair_t *r = NEW(lib_pair_t);
          r->link.tag = LIB_PAIR;
          r->libs[0] = OR(left, libs[0]);
          r->libs[1] = OR(right, libs[1]);
          return &r->link;
      }

      case LIB_SHIFT: {
          lib_shift_t *l = DEOFFSET(lib_shift_t, link, lib);
          assert (l->shift && "should never have shift by 0");

          subst_shift_t ss;
          subst_shift(&ss, l->shift, subst);

          if (!ss.link.next) {
              if (ss.shift == l->shift) {
                  /* I think this case should never happen. */
                  assert(0 && "impossible?");
                  /* But if it does, this is the way to handle it. */
                  return NULL;
              }

              /* We're just doing a shift. */
              return shift_lib(l->inner, ss.shift);
          }

          return lib_subst(&ss.link, l->inner);
      }

      case LIB_LAMBDA: {
          lib_t *body = DEOFFSET(lib_lambda_t, link, lib)->body;
          subst_var_t vs = { .tag = SUBST_VAR, .next = subst };

          body = lib_subst(&vs, body);
          if (!body) return NULL;

          lib_lambda_t *r = NEW(lib_lambda_t);
          r->link.tag = LIB_LAMBDA;
          r->body = body;
          return &r->link;
      }

      case LIB_CODE_FUNC:
        assert (0 && "unimplemented");

      case LIB_CODE_LIB: {
          lib_t *inner =
              lib_subst(subst, DEOFFSET(lib_code_lib_t, link, lib)->val);
          if (!inner)
              return NULL;

          lib_code_lib_t *r = NEW(lib_code_lib_t);
          r->link.tag = LIB_CODE_LIB;
          r->val = inner;
          return &r->link;
      }

      case LIB_CODE_INT:
      case LIB_CODE_STRING:
        return NULL;
    }

    assert(0 && "unrecognized lib tag");
}

lib_t *subst(subst_t *subst, lib_t *lib) {
    if (!subst)
        /* Identity. */
        return lib;
    lib_t *result = lib_subst(subst, lib);
    return OR(result, lib);
}


/* The main loop. */
void run(state_t *S) {
    for (;;) {
#define IP (&S->ip)
#define ENV (&S->env)
#define STK (&S->stack)
#define PUSH stack_push(STK)
#define POP  stack_pop(STK)
#define SUBST (S->env.libsubst)

        switch ((enum op) read_op(IP)) {
          case OP_NOP: break;

          case OP_ACCESS: {
            shift_t idx = read_shift(IP);
            val_t *slot = PUSH;
            env_access(ENV, idx, slot);
            break;
          }

          case OP_CLOSE: {
              stack_push_closure(STK, read_block(IP), S->env);
              break;
          }

          case OP_FUNC: {
              static env_t empty = { .valenv = NULL, .libsubst = NULL };
              stack_push_closure(STK, read_block(IP), empty);
              break;
          }

          case OP_APPLY: {
              frame_t *frame = NEW(frame_t);
              frame->ip = S->ip;
              frame->env = S->env;

              val_t arg = POP;
              val_t func = POP;
              val_t *frameval = PUSH;
              assert (func.tag == VAL_CLOSURE);

              /* Push return frame. */
              frameval->tag = VAL_FRAME;
              frameval->data.frame = frame;

              /* Jump into closure, pushing arg into env. */
              closure_t *clos = func.data.closure;
              S->ip = clos->block;
              S->env = clos->env;
              env_push(ENV, arg);
              break;
          }

          case OP_RET: {
              if (stack_empty(STK))
                  /* End of program. */
                  return;

              val_t v = POP;
              assert (v.tag == VAL_FRAME);
              frame_t *frame = v.data.frame;
              S->ip = frame->ip;
              S->env = frame->env;
              break;
          }

          case OP_CONST_INT: {
              stack_push_int(STK, read_int(IP));
              break;
          }

          case OP_CONST_STRING: {
              val_t *p = PUSH;
              p->tag = VAL_STRING;
              p->data.str = read_string(IP);
              break;
          }

          case OP_LIB: {
              val_t *p = PUSH;
              p->tag = VAL_LIB;
              p->data.lib = subst(SUBST, read_lib(IP));
              break;
          }

          case OP_USE: {
              atom_t *atom = read_atom(IP);
              lib_t *lib = NULL;
              bool gotlib = atom_subst(SUBST, atom, &atom, &lib);
              assert (gotlib && lib);
              (void) gotlib; /* unused if NDEBUG */
              val_t *slot = PUSH;

              switch (lib->tag) {
                case LIB_CODE_FUNC: {
                    lib_code_func_t *func =
                        DEOFFSET(lib_code_func_t, link, lib);
                    (void) func;
                    assert (0 && "unimplemented");
                    break;
                }

                case LIB_CODE_LIB:
                  slot->tag = VAL_LIB;
                  slot->data.lib = DEOFFSET(lib_code_lib_t, link, lib)->val;
                  break;

                case LIB_CODE_INT:
                  slot->tag = VAL_INT;
                  slot->data.num = DEOFFSET(lib_code_int_t, link, lib)->val;
                  break;

                case LIB_CODE_STRING:
                  slot->tag = VAL_STRING;
                  slot->data.str = DEOFFSET(lib_code_str_t, link, lib)->val;
                  break;

                case LIB_ATOM: case LIB_PAIR: case LIB_LAMBDA: case LIB_SHIFT:
                  assert(0 && "impossible");
              }
            break;
          }

          case OP_LOAD: {
              val_t vlib = POP;
              assert (vlib.tag == VAL_LIB);
              lib_t *lib = vlib.data.lib;
              subst_t *oldsubst = SUBST;
              subst_lib_t *subst = NEW(subst_lib_t);
              subst->link.tag = SUBST_LIB;
              subst->link.next = oldsubst;
              subst->lib = lib;
              SUBST = &subst->link;
              break;
          }

          case OP_ADD:
          case OP_SUB:
          case OP_MUL:
          case OP_DIV:
          case OP_CONCAT:
          case OP_PRINT:
            assert(0 && "unimplemented");

          default:
            assert(0 && "unrecognized opcode");
        }
    }
}

int main(int argc, char **argv)
{
    fprintf(stderr, "unimplemented, sorry\n");
    return 0;
    (void) argc, (void) argv;
}
