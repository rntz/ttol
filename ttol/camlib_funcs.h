#ifndef _CAMLIB_FUNCS_H_
#define _CAMLIB_FUNCS_H_

#include "camlib_types.h"

env_t empty_env;

/* Library manipulation */
atom_t *shift_atom(atom_t *atom, shift_t shift);

lib_t *shift_lib(lib_t *lib, shift_t shift);
shift_t unshift_lib(lib_t **libp);


/* Substitutions */
shift_t subst_get_shift(subst_t *subst);

bool subst_lookup(subst_t *subst, shift_t var, atom_t **atomp, lib_t **libp);

/* Return value can safely be ignored if `shift > 0'. */
subst_t *subst_shift(subst_shift_t *s, shift_t shift, subst_t *orig);

bool atom_subst_fast(
    subst_t *subst, atom_t *atom, atom_t **atomp, lib_t **libp);
bool atom_subst(
    subst_t *subst, atom_t *atom, atom_t **atomp, lib_t **libp);

block_t *block_subst(subst_t *subst, block_t *block);
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

void stack_push_closure(stack_t *stack, block_t *block, env_t env);

void state_init(state_t *state, ip_t ip);

#endif
