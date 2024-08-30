.PHONY: all html clean Everything.agda

RTSOPTS = +RTS -M6G -A128M -RTS

all: html

html: index.agda
	agda ${RTSOPTS} --html --html-dir=public index.agda -i.

agda: index.agda
	agda ${RTSOPTS} index.agda -i.

clean:
	find . -name '*.agdai' -exec rm \{\} \;
