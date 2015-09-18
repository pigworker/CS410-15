default: CS410-notes.pdf

CS410-notes.pdf: FORCE
	pushd notes ; make ; popd

FORCE:
