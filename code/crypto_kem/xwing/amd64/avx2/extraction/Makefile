
JASMIN2ECC ?= jasminc
JINCLUDE_MLKEM  := -I Kyber:../../../../../../formosa-mlkem/code/jasmin/
JINCLUDE_KECCAK := -I Keccak:../../../../../../formosa-keccak/src/amd64/
JINCLUDE_X25519 := -I formosa25519:../../../../../../formosa-25519/src/


.PHONY: all ec clean

all: ec

ec:
	jasminc ../jkem.jazz -oec xkem_avx2.ec \
	  -ec jade_kem_xwing_xwing_amd64_avx2_keypair_derand \
	  -ec jade_kem_xwing_xwing_amd64_avx2_enc_derand \
	  -ec jade_kem_xwing_xwing_amd64_avx2_dec \
		$(JINCLUDE_MLKEM) $(JINCLUDE_X25519) $(JINCLUDE_KECCAK) \
		-oecarray Arrays/

clean:
	rm -f *.ec
