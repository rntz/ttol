# Some directories.
ROOT=
PREFIX=$(ROOT)/usr/local
LIB=$(PREFIX)/lib
INCLUDE=$(PREFIX)/include

# Variables affecting compilation.
CC=gcc
CCLD=$(CC)
AR=ar
CFLAGS+= -std=c99 -pedantic -Wall -Wextra -Werror -pipe -Wswitch-enum
CFLAGS+= -O0 -ggdb3
# LIBS is defined in Makefile
LDFLAGS+= $(addprefix -l,$(LIBS))

# Directories to search for things.
INCLUDE_DIRS+= $(INCLUDE)
LIB_DIRS+= $(LIB)
CFLAGS+= $(addprefix -I,$(INCLUDE_DIRS))
LDFLAGS+= $(addprefix -L,$(LIB_DIRS))


# For building with clang. Notably, don't have to change any compilation flags.
# NB. Compiling with clang gives nicer compilation error messages, but forfeits
# the ability to use macros from gdb.
#CC=clang
