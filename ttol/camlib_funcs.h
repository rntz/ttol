#ifndef _CAMLIB_FUNCS_H_
#define _CAMLIB_FUNCS_H_

#include "camlib_types.h"

/* Reading from bytecode stream */
op_t    read_op(ip_t *ip);
shift_t read_shift(ip_t *ip);
int_t   read_int(ip_t *ip);
lib_t  *read_lib(ip_t *ip);
atom_t *read_atom(ip_t *ip);
ip_t    read_block(ip_t *ip);
char   *read_string(ip_t *ip);


/* Library manipulation */
atom_t *shift_atom(atom_t *atom, shift_t shift);

lib_t *shift_lib(lib_t *lib, shift_t shift);
lib_t *unshift_lib(lib_t *lib, shift_t *out);

/* Substitutions */
/* precondition: subst is a subst_shift */
shift_t subst_get_shift(subst_t *subst);
/* precondition: subst is a subst_lib */
lib_t *subst_get_lib(subst_t *subst);

bool subst_lookup(subst_t *subst, shift_t var, atom_t **atomp, lib_t **libp);

void subst_shift(subst_shift_t *s, shift_t shift, subst_t *orig);

bool atom_subst_fast(
    subst_t *subst, atom_t *atom, atom_t **atomp, lib_t **libp);
bool atom_subst(
    subst_t *subst, atom_t *atom, atom_t **atomp, lib_t **libp);
lib_t *atom_subst_lib(subst_t *subst, atom_t *atom);

lib_t *lib_subst(subst_t *subst, lib_t *lib);
lib_t *subst(subst_t *subst, lib_t *lib);


/* Stack & environment manipulation. */
void env_access(env_t *env, shift_t idx, val_t *out);
void env_push(env_t *env, val_t val);

bool stack_empty(stack_t *stack);
val_t stack_pop(stack_t *stack);
val_t *stack_push(stack_t *stack);

int_t stack_pop_int(stack_t *stack);
void stack_push_int(stack_t *stack, int_t val);
char *stack_pop_string(stack_t *stack);

void stack_push_closure(stack_t *stack, ip_t block, env_t env);

void state_init(state_t *state, ip_t ip);

#endif
