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


/* Substitution manipulation */
lib_t *subst(subst_t *subst, lib_t *lib) {
    assert(0 && "unimplemented");
    (void) subst, (void) lib;
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
