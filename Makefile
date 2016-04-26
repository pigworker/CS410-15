default: CS410-notes.pdf

Ex6Edit: Ex6Edit.agda ANSIEscapes.hs HaskellSetup.hs Ex6AgdaSetup.agda
	agda --compile --ghc-flag "-lncurses" Ex6Edit.agda

Ex6App: Ex6App.agda ANSIEscapes.hs HaskellSetup.hs Ex6AgdaSetup.agda
	agda --compile --ghc-flag "-lncurses" Ex6App.agda

CS410-notes.pdf: FORCE
	pushd notes ; make ; popd

edit: Ex6Edit
	./Ex6Edit

app: Ex6App
	./Ex6App

FORCE:
