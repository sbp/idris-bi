all: Bi.ipkg
	idris --build Bi.ipkg

check: src/Data/Bip/Proofs.ibc
	idris -i src --check src/Data/Bip/Proofs.idr
	idris -i src --check src/Data/Bin/Proofs.idr

clean: ;
	find . -name '*.i[bd]c' -type f -delete
