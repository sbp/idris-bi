all: Bi.ipkg
	idris --build Bi.ipkg

check: src/Data/Bip/Proofs.ibc
	idris -i src --check src/Data/Bip/Proofs.idr
