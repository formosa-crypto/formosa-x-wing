
JASMIN2ECC ?= jasminc
JINCLUDE_MLKEM  := -I formosamlkem:../../../../../../formosa-mlkem/code/jasmin/mlkem_avx2/
JINCLUDE_X25519 := -I formosa25519:../../../../../../formosa-25519/src/


.PHONY: all ec clean

all: ec

ec:
	jasminc ../jkem.jazz -oec jkem_avx2.ec \
	  -ec jade_kem_xwing_xwing_amd64_avx2_keypair \
	  -ec jade_kem_xwing_xwing_amd64_avx2_enc \
	  -ec jade_kem_xwing_xwing_amd64_avx2_dec \
		$(JINCLUDE_MLKEM) $(JINCLUDE_X25519) \
		-oecarray Arrays/

clean:
	rm -f *.ec
