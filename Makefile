CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe
OS      := $(shell uname -s)
JASMINC ?= jasminc
JFLAGS  ?= -lazy-regalloc

JINCLUDE_MLKEM  :=  -I Formosa_MLKEM:formosa-mlkem/code/jasmin/mlkem_avx2/
JINCLUDE_X25519 :=  -I Formosa_X25519:formosa-25519/src/crypto_scalarmult/curve25519/amd64/mulx/
XWING_SRC       := code/crypto_kem/xwing/amd64/avx2


%.s: %.jazz
	$(JASMINC) $(JFLAGS) -o $@ $(JFLAGS) $(JINCLUDE) $^
