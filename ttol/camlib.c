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
    return &l->link;
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

/* returns true and sets libp if result is library.
 * returns false and sets atomp if result is atom.
 * sets atomp to NULL if result atom is same as input.
 */
bool atom_subst(subst_t *subst, atom_t *atom, atom_t **atomp, lib_t **libp) {
    assert (0 && "unimplemented");
    (void) subst, (void) atom, (void) atomp, (void) libp;
}

/* returns NULL if no copy was necessary. */
lib_t *lib_subst(subst_t *subst, lib_t *lib) {
    assert (subst);

    switch (lib->tag) {
      case LIB_ATOM: {
          atom_t *atom = DEOFFSET(lib_atom_t, link, lib)->atom;
          lib_t *rlib;
          if (atom_subst(subst, atom, &atom, &rlib))
              return rlib;
          if (!atom)
              return NULL;

          /* Make new lib wrapping atom. */
          lib_atom_t *r = NEW(lib_atom_t);
          r->link.tag = LIB_ATOM;
          r->atom = atom;
          return &r->link;
      }

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

      case LIB_CODE:
        assert(0 && "unimplemented");
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

        switch ((enum op) read_op(IP)) {
          case OP_NOP: break;

          case OP_ACCESS: {
            shift_t idx = read_shift(IP);
            val_t *slot = PUSH;
            env_access(ENV, idx, slot);
            break;
          }

          case OP_CLOSE: {
            closure_t *clos = NEW(closure_t);
            clos->block = read_block(IP);
            clos->env = S->env;

            val_t *slot = PUSH;
            slot->tag = VAL_CLOSURE;
            slot->data.closure = clos;
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
              p->data.lib = subst(S->env.libsubst, read_lib(IP));
              break;
          }

          case OP_USE:
          case OP_LOAD:
          case OP_FUNC:

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
