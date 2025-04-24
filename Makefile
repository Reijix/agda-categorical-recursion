.PHONY: all html clean Everything.agda

RTSOPTS = +RTS -M6G -A128M -RTS

IDM = hy84coky
HOST = cip1d1.cip.cs.fau.de

all: html

html: index.agda
	agda ${RTSOPTS} --html --html-dir=agda-categorical-recursion index.agda -i.

agda: index.agda
	agda ${RTSOPTS} index.agda -i.

push: all
	scp -r agda-categorical-recursion ${IDM}@${HOST}:.www/agda-stuff/

clean:
	find . -name '*.agdai' -exec rm \{\} \;