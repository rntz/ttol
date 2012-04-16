#ifndef _CAMLIB_H_
#define _CAMLIB_H_

#include <stdint.h>
#include <stddef.h>

typedef uint32_t shift_t;
typedef int32_t int_t;

typedef enum { LIB_ATOM, LIB_PAIR, LIB_LAMBDA, LIB_CODE, LIB_SHIFT } lib_tag_t;
typedef struct { lib_tag_t tag; } lib_t;

typedef enum { ATOM_VAR, ATOM_APP, ATOM_PROJ, ATOM_SHIFT } atom_tag_t;
typedef struct { atom_tag_t tag; } atom_t;


/* Library substitutions. */
typedef enum { SUBST_LIB, SUBST_VAR, SUBST_SHIFT } subst_tag_t;
typedef struct subst_link subst_t;
struct subst_link { subst_tag_t tag; subst_t *next; };

typedef subst_t subst_var_t;    /* no extra info */

typedef struct {
    subst_t link;
    shift_t shift;
} subst_shift_t;

typedef struct {
    subst_t link;
    lib_t *lib;
} subst_lib_t;

/* precondition: subst is a subst_shift */
shift_t subst_shift(subst_t *subst);
/* precondition: subst is a subst_lib */
lib_t *subst_lib(subst_t *subst);


/* We shouldn't actually need tags on values, since the source language is
 * statically typed. But:
 *
 * a. It might help catch bugs in the interpreter itself. This is the big
 *    reason.
 *
 * b. If we ever want a precise gc, they'll be useful. Precise gc can be done
 *    w/o object tags, but it's a PITA.
 *
 * c. This isn't meant to be a /fast/ interpreter.
 */
typedef enum { VAL_INT, VAL_STRING, VAL_CLOSURE, VAL_LIB, VAL_FRAME } val_tag_t;

typedef struct closure closure_t;
typedef struct frame frame_t;

typedef struct {
    val_tag_t tag;
    union {
        int_t num;
        char *str;
        lib_t *lib;
        closure_t *closure;
        frame_t *frame;
    } data;
} val_t;


/* Instructions. */
typedef uint8_t op_t;
typedef op_t *ip_t;
enum op {
    /* Basic CAM instructions. */
    OP_ACCESS,
    OP_CLOSE,
    OP_APPLY,
    OP_RET,
    /* Primitives. */
    OP_ADD, OP_SUB, OP_MUL, OP_DIV,
    OP_CONCAT, OP_PRINT,
    /* Constant loaders */
    OP_CONST_INT, OP_CONST_STRING,
    /* Library-related instructions. */
    OP_LIB, OP_USE, OP_LOAD, OP_FUNC,
    /* Needed to pad replaced "use" instructions. */
    OP_NOP,
};


/* Runtime state */
typedef struct valenv valenv_t;
struct valenv {
    val_t val;
    valenv_t *next;
};

typedef struct {
    valenv_t *valenv;           /* Value env. */
    subst_t libsubst;           /* lib env. */
} env_t;

struct closure { ip_t block; env_t env; };
struct frame { ip_t block; env_t env; };

/* Stack. */
typedef struct stack_frag stack_frag_t;
struct stack_frag {
    size_t size;
    stack_frag_t *next;
    val_t vals[];
};

typedef struct {
    val_t *sp;
    val_t *top;
    /* Number of values between sp and bottom of first stack frag. */
    size_t len;
} stack_t;

/* static inline stack_frag_t *stack_frag(stack_t *stack) {
 *     return (stack_frag_t*) (((char*) stack->top) - offsetof(stack_frag, vals));
 * } */

stack_frag_t *stack_frag(stack_t *stack);
void stack_pop(stack_t *stack, val_t *val);
val_t *stack_push(stack_t *stack);

typedef struct {
    ip_t ip;
    env_t env;
    stack_t stack;
} state_t;

#endif
