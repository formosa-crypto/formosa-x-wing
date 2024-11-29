CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe
OS      := $(shell uname -s)
JASMINC ?= jasminc
JFLAGS  ?= -lazy-regalloc

JINCLUDE_MLKEM  :=  -I formosamlkem:formosa-mlkem/code/jasmin/mlkem_avx2/
JINCLUDE_X25519 :=  -I formosa25519:formosa-25519/src/

XWING_SRC       := code/crypto_kem/xwing/amd64/avx2


$(XWING_SRC)/jkem.s : $(XWING_SRC)/jkem.jazz
	$(JASMINC) $(JFLAGS) -o $@ $(JFLAGS) $(JINCLUDE_MLKEM) $(JINCLUDE_X25519) $^
