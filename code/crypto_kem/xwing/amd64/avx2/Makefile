CC      ?= clang
CFLAGS := -Wall -Wextra -g -O3 -fomit-frame-pointer
OS      := $(shell uname -s)
JASMINC ?= jasminc
JFLAGS  ?= -lazy-regalloc

JASMINC ?= jasminc
JFLAGS  ?= -lazy-regalloc
JINCLUDE_MLKEM  := -I formosamlkem:../../../../../formosa-mlkem/code/jasmin/mlkem_avx2/
JINCLUDE_X25519 := -I formosa25519:../../../../../formosa-25519/src/

XWING_SRC := .
XWING_TEST_SRC := $(XWING_SRC)/test
TEST_HEADERS := $(XWING_TEST_SRC)/test_vectors.h $(XWING_TEST_SRC)/test_kem.h
TEST_SOURCES := $(XWING_TEST_SRC)/test_kem.c

$(XWING_SRC)/jkem.s : $(XWING_SRC)/jkem.jazz
	$(JASMINC) $(JFLAGS) -o $@ $(JFLAGS) $(JINCLUDE_MLKEM) $(JINCLUDE_X25519) $^

$(XWING_SRC)/test/test_kem: $(TEST_SOURCES) $(TEST_HEADERS) $(XWING_SRC)/jkem.s
	$(CC) $(CFLAGS) $(TEST_SOURCES) $(XWING_SRC)/jkem.s -o $@

asm:  $(XWING_SRC)/jkem.s 
test: $(XWING_SRC)/test/test_kem

clean:
	-rm -f jkem.s
	-rm -f $(XWING_TEST_SRC)/test_kem
