#ifndef _CAMLIB_TYPES_H_
#define _CAMLIB_TYPES_H_

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

typedef uint32_t shift_t;
typedef int32_t int_t;

typedef enum {
    LIB_ATOM, LIB_PAIR, LIB_LAMBDA, LIB_SHIFT,
    LIB_CODE_FUNC, LIB_CODE_LIB, LIB_CODE_INT, LIB_CODE_STRING
} lib_tag_t;
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


/* We shouldn't actually need tags on values, since the source language is
 * statically typed. But it might help catch bugs in the interpreter, so we
 * leave them in.
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
typedef uint8_t *ip_t;
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
    subst_t *libsubst;          /* Lib env. */
} env_t;

struct closure { ip_t block; env_t env; };
struct frame { ip_t ip; env_t env; };

/* Stack. */
typedef struct {
    val_t *sp;
    val_t *start;
    size_t size;
} stack_t;

typedef struct {
    ip_t ip;
    env_t env;
    stack_t stack;
} state_t;


/* Libraries */
typedef struct { lib_t link; atom_t *atom; } lib_atom_t;
typedef struct { lib_t link; lib_t *libs[2]; } lib_pair_t;
typedef struct { lib_t link; shift_t shift; lib_t *inner; } lib_shift_t;
typedef struct { lib_t link; lib_t *body; } lib_lambda_t;
typedef struct { lib_t link; int_t val; } lib_code_int_t;
typedef struct { lib_t link; char *val; } lib_code_str_t;
typedef struct { lib_t link; lib_t *val; } lib_code_lib_t;

enum linkop { LINKOP_LOAD, LINKOP_USE, LINKOP_FUNC, LINKOP_OTHER_INSTR };

typedef struct {
    size_t instrs_len;
    size_t linkops_len;
    uint8_t *linkops;
    op_t instrs[];
} block_t;

typedef struct {
    lib_t link;
    block_t *block;
} lib_code_func_t;

/* Atoms */
typedef struct { atom_t link; shift_t var; } atom_var_t;
typedef struct { atom_t link; atom_t *func; lib_t *arg; } atom_app_t;
typedef struct { atom_t link; shift_t shift; atom_t *inner; } atom_shift_t;

/* for dir, false = left, true = right */
typedef struct { atom_t link; bool dir; atom_t *inner; } atom_proj_t;

#endif
