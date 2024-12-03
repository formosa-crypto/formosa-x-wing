XWING_SRC := code/crypto_kem/xwing/amd64/avx2

.PHONY: default jasmin extract clean_eco clean_asm clean

default: jasmin 

jasmin:
	make -C $(XWING_SRC)/ asm

test:
	make -C $(XWING_SRC)/ test

extract:
	make -C $(XWING_SRC)/extraction

clean_asm:
	-rm -f $(XWING_SRC)/jkem.s

clean_eco:
	find proof -name '*.eco' -exec rm '{}' ';'

clean: clean_asm clean_eco
