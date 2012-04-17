/* WARNING.
 *
 * This code is too long, too untested, and too complicated to be bug-free.
 */

/* slz is a serialization library. see http://github.com/rntz/slz */
#include "camlib.h"

#include <gc.h>
#include <slz.h>

#include <alloca.h>
#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define INIT_STACK_SIZE 1024

#define NEW(typ) GC_MALLOC(sizeof(typ))

#define DEOFFSET(typ, mem, ptr) ((typ*)(((char*)(ptr)) - offsetof(typ, mem)))

#define ALIGN_UPTO(X, ALIGN)                                    \
    ((X) % (ALIGN) ? (X) + (ALIGN) - ((X) % (ALIGN)) : (X))


/* Miscellany. */
env_t empty_env = { .valenv = NULL, .libsubst = NULL };


/* Reading things from bytecode stream. */
#define NEXT(ipp) *((*(ipp))++)
op_t read_op(ip_t *ipp) { return NEXT(ipp); }
void write_op(ip_t *ipp, op_t op) { NEXT(ipp) = op; }

void read_aligned(ip_t *ipp, char *out, size_t size) {
    unsigned char *p = *ipp;
    p = (unsigned char*) ALIGN_UPTO((uintptr_t) p, size);
    memcpy(out, p, size);
    *ipp = p + size;
}

void write_aligned(ip_t *ipp, char *in, size_t size) {
    unsigned char *p = *ipp;
    p = (unsigned char*) ALIGN_UPTO((uintptr_t) p, size);
    memcpy(p, in, size);
    *ipp = p + size;
}

#define READER_WRITER(type, name)                               \
    type read_##name(ip_t *ipp) {                               \
        type val;                                               \
        read_aligned(ipp, (char*)&val, sizeof(type));           \
        return val;                                             \
    }                                                           \
    void write_##name(ip_t *ipp, type val) {                    \
        write_aligned(ipp, (char*)&val, sizeof(type));          \
    }

READER_WRITER(shift_t, shift)
READER_WRITER(int_t, int)
READER_WRITER(lib_t*, lib)
READER_WRITER(atom_t*, atom)
READER_WRITER(ip_t, ip)
READER_WRITER(char*, string)


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
        size_t newsize = stack->size * 2;
        assert (stack->size < newsize);
        stack->size = newsize;
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

char *stack_pop_string(stack_t *stack) {
    val_t v = stack_pop(stack);
    assert (v.tag == VAL_STRING);
    return v.data.str;
}

void stack_push_int(stack_t *stack, int_t val) {
    val_t *p = stack_push(stack);
    p->tag = VAL_INT;
    p->data.num = val;
}

void stack_push_closure(stack_t *stack, ip_t instrs, env_t env) {
    closure_t *clos = NEW(closure_t);
    clos->instrs = instrs;
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

shift_t unshift_lib(lib_t **libp) {
    if ((*libp)->tag != LIB_SHIFT)
        return 0;
    lib_shift_t *l = DEOFFSET(lib_shift_t, link, *libp);
    assert (l->inner->tag != LIB_SHIFT && "no nested lib_shifts");
    *libp = l->inner;
    return l->shift;
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

    lib_t *l = *libp;
    shift_t shift = unshift_lib(&l);
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
    /* should be avoiding trivial substitutions. */
    assert (subst);
    assert (subst->tag != SUBST_SHIFT || subst->next);

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
                  assert (0 && "impossible?");
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
          shift_t shift = unshift_lib(&lib);
          assert (lib->tag == LIB_PAIR);
          *libp = shift_lib(
              DEOFFSET(lib_pair_t, link, lib)->libs[proj->dir], shift);
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
          shift_t shift = unshift_lib(&funclib);
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
    assert (subst->tag != SUBST_SHIFT || subst->next);

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
                  assert (0 && "impossible?");
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

      case LIB_CODE_FUNC: {
          block_t *block =
              block_subst(subst, DEOFFSET(lib_code_func_t, link, lib)->block);
          if (!block)
              return NULL;

          lib_code_func_t *r = NEW(lib_code_func_t);
          r->link.tag = LIB_CODE_FUNC;
          r->block = block;
          return &r->link;
      }

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

void ensure_block_init_from(block_t **outblock, block_t *inblock) {
    if (*outblock)
        return;
    size_t size = sizeof(block_t) + inblock->instrs_len;
    block_t *b = *outblock = GC_MALLOC(size);
    b->instrs_len = inblock->instrs_len;
    memcpy(b->instrs, inblock->instrs, inblock->instrs_len);
}

block_t *block_subst(subst_t *subst, block_t *block) {
    block_t *res = NULL;
    uint8_t *rlinkop = block->linkops;
    uint8_t *end = rlinkop + block->linkops_len;
    uint8_t *res_linkops = GC_MALLOC(block->linkops_len);
    uint8_t *wlinkop = res_linkops;

    while (rlinkop < end) {
        op_t op = read_op(&rlinkop);
        ip_t wlinkop_old = wlinkop;
        write_op(&wlinkop, op);

        switch ((enum linkop) op) {
          case LINKOP_LOAD: {
              subst_var_t *sv = alloca(sizeof(subst_var_t));
              sv->next = subst;
              subst = sv;
              break;
          }

          case LINKOP_USE:
            /* Uses don't have a shift, but since they can turn into funcs they
             * are followed by a slot for one.
             */
          case LINKOP_FUNC: (void) 0;
            shift_t shift = read_shift(&rlinkop);

          case LINKOP_OTHER_INSTR: {
              ip_t interp = read_ip(&rlinkop);
              op_t op = read_op(&interp);
              size_t off = interp - block->instrs;

              switch (op) {
                case OP_LIB: {
                    assert (op == LINKOP_OTHER_INSTR);
                    lib_t *lib = lib_subst(subst, read_lib(&interp));
                    if (!lib)
                        break;
                    ensure_block_init_from(&res, block);
                    ip_t wip = res->instrs + off;
                    write_lib(&wip, lib);
                    break;
                }

                case OP_CLOSE: {
                    assert (op == LINKOP_OTHER_INSTR);
                    ip_t clos_ip = read_ip(&interp);
                    block_t *clos_block =
                        block_subst(subst, DEOFFSET(block_t, instrs, clos_ip));
                    if (!clos_block)
                        break;
                    ensure_block_init_from(&res, block);
                    ip_t wip = res->instrs + off;
                    write_ip(&wip, clos_block->instrs);
                    break;
                }

                case OP_FUNC: {
                    assert (op == LINKOP_FUNC);
                    ip_t func_ip = read_ip(&interp);
                    block_t *func_block = DEOFFSET(block_t, instrs, func_ip);

                    subst_shift_t ss;
                    subst_shift(&ss, shift, subst);

                    if (!ss.link.next) {
                        /* Just a shift. */
                        write_shift(&wlinkop, ss.shift);
                        break;
                    }

                    write_shift(&wlinkop, 0);
                    func_block = block_subst(&ss.link, func_block);
                    if (!func_block)
                        break;

                    ensure_block_init_from(&res, block);
                    ip_t wip = res->instrs + off;
                    write_ip(&wip, func_block->instrs);
                    break;
                }

                case OP_USE: {
                    assert (op == LINKOP_USE);
                    atom_t *atom = read_atom(&interp);
                    lib_t *lib;
                    if (!atom_subst(subst, atom, &atom, &lib)) {
                        if (!atom)
                            break;
                        ensure_block_init_from(&res, block);
                        ip_t wip = res->instrs + off;
                        write_atom(&wip, atom);
                        break;
                    }

                    /* Got a library. Replace the USE (use-code elimination). */
                    shift_t shift = unshift_lib(&lib);
                    ensure_block_init_from(&res, block);
                    /* -1 to make wip point to the USE instruction itself. */
                    ip_t wip = res->instrs + off - 1;
                    /* Need to change linkop from USE to appropriate value. */
                    wlinkop = wlinkop_old;

                    switch (lib->tag) {
                      case LIB_CODE_FUNC: {
                          /* change linkop to FUNC. */
                          write_op(&wlinkop, LINKOP_FUNC);
                          write_shift(&wlinkop, shift);

                          /* write new func instr */
                          write_op(&wip, OP_FUNC);
                          block_t *func_block =
                              DEOFFSET(lib_code_func_t, link, lib)->block;
                          write_ip(&wip, func_block->instrs);
                          break;
                      }

                      case LIB_CODE_LIB: {
                          /* change linkop to OTHER_INSTR. */
                          write_op(&wlinkop, LINKOP_OTHER_INSTR);

                          /* write new lib instr */
                          write_op(&wip, OP_LIB);
                          lib = DEOFFSET(lib_code_lib_t, link, lib)->val;
                          write_lib(&wip, shift_lib(lib, shift));
                          break;
                      }

                      case LIB_CODE_INT:
                        /* no linkop needed. */
                        write_op(&wip, OP_CONST_INT);
                        write_int(&wip,
                                  DEOFFSET(lib_code_int_t, link, lib)->val);
                        break;

                      case LIB_CODE_STRING:
                        write_op(&wip, OP_CONST_STRING);
                        write_string(&wip,
                                     DEOFFSET(lib_code_str_t, link, lib)->val);
                        break;

                      case LIB_ATOM: case LIB_PAIR: case LIB_LAMBDA:
                      case LIB_SHIFT:
                        assert (0 && "impossible");

                      default: assert (0 && "unrecognized lib tag");
                    }
                    break;
                }

                default:
                  assert (0 && "invalid op code for linkop");
              }
              break;
          }

          default:
            assert(0 && "unrecognized linkop");
            (void) wlinkop, (void) block, (void) subst;
        }
    }

    if (!res)
        return NULL;

    res->linkops = res_linkops;
    res->linkops_len = wlinkop - res_linkops;
    return res;
}

lib_t *subst(subst_t *subst, lib_t *lib) {
    if (!subst)
        /* Identity. */
        return lib;
    lib_t *result = lib_subst(subst, lib);
    return OR(result, lib);
}


/* The main loop. */
val_t run(state_t *S) {
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
              stack_push_closure(STK, read_ip(IP), S->env);
              break;
          }

          case OP_FUNC: {
              stack_push_closure(STK, read_ip(IP), empty_env);
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
              S->ip = clos->instrs;
              S->env = clos->env;
              env_push(ENV, arg);
              break;
          }

          case OP_RET: {
              val_t result = POP;
              if (stack_empty(STK))
                  /* End of program. */
                  return result;

              val_t v = POP;
              assert (v.tag == VAL_FRAME);
              frame_t *frame = v.data.frame;
              S->ip = frame->ip;
              S->env = frame->env;
              *PUSH = result;
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
              bool gotlib = atom_subst_fast(SUBST, atom, &atom, &lib);
              assert (gotlib && lib);
              (void) gotlib; /* unused if NDEBUG */
              val_t *slot = PUSH;

              switch (lib->tag) {
                case LIB_CODE_FUNC: {
                    block_t *blk = DEOFFSET(lib_code_func_t, link, lib)->block;
                    closure_t *clos = NEW(closure_t);
                    clos->instrs = blk->instrs;
                    clos->env = empty_env;
                    slot->tag = VAL_CLOSURE;
                    slot->data.closure =clos;
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

                default: assert (0 && "unrecognized lib tag");
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

#define INTOP(OP) {                             \
                int_t y = stack_pop_int(STK);   \
                int_t x = stack_pop_int(STK);   \
                stack_push_int(STK, x OP y);    \
                break;                          \
            }

          case OP_ADD: INTOP(+);
          case OP_SUB: INTOP(-);
          case OP_MUL: INTOP(*);
          case OP_DIV: INTOP(/);

          case OP_CONCAT: {
              char *y = stack_pop_string(STK);
              char *x = stack_pop_string(STK);
              size_t xlen = strlen(x), ylen = strlen(y);
              /* NB. GC_MALLOC_ATOMIC informs the GC that there will never be
               * pointers in the allocated region.
               */
              char *xy = GC_MALLOC_ATOMIC(xlen + ylen + 1);
              memcpy(xy, x, xlen);
              memcpy(xy + xlen, y, ylen);
              xy[xlen+ylen] = '\0';
              assert (strlen(xy) == xlen + ylen);

              val_t *slot = PUSH;
              slot->tag = VAL_STRING;
              slot->data.str = xy;
              break;
          }

          case OP_PRINT: {
              char *s = stack_pop_string(STK);
              printf("%s\n", s);
              break;
          }

          default:
            assert(0 && "unrecognized opcode");
        }
    }
}

void state_init(state_t *S, ip_t ip) {
    S->ip = ip;
    S->env.valenv = NULL;
    S->env.libsubst = NULL;
    S->stack.size = INIT_STACK_SIZE;
    S->stack.start = S->stack.sp = GC_MALLOC(S->stack.size * sizeof(val_t));
}


/* A simple test. */
int main(int argc, char **argv)
{
    GC_INIT();

    uint8_t instrs[1024];
    ip_t ip = instrs;
    write_op    (&ip, OP_CONST_STRING);
    write_string(&ip, "testing");
    write_op    (&ip, OP_PRINT);
    write_op    (&ip, OP_CONST_INT);
    write_int   (&ip, -1);
    write_op    (&ip, OP_RET);

    state_t S;
    state_init(&S, instrs);
    val_t res = run(&S);

    if (res.tag == VAL_STRING)
        printf("returned string: %s\n", res.data.str);
    else if (res.tag == VAL_INT)
        printf("returned int: %d\n", res.data.num);
    else
        printf("returned unprintable value with tag %d\n", res.tag);

    return 0;
    (void) argc, (void) argv;
}
