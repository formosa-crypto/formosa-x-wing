JASMINC ?= jasminc
JFLAGS  ?= -lazy-regalloc
JINCLUDE_MLKEM  := -I formosamlkem:../../../../../formosa-mlkem/code/jasmin/mlkem_avx2/
JINCLUDE_X25519 := -I formosa25519:../../../../../formosa-25519/src/

XWING_SRC       := .

$(XWING_SRC)/jkem.s : $(XWING_SRC)/jkem.jazz
	$(JASMINC) $(JFLAGS) -o $@ $(JFLAGS) $(JINCLUDE_MLKEM) $(JINCLUDE_X25519) $^

