default: CS410-notes.pdf

CS410-notes.pdf: notes/Introduction.lagda
	pushd notes ; make ; popd
