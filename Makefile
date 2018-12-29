SRC := ${PWD}/n2o
OUT := ${PWD}/dist
DEP := -package network-2.6.3.6
GHC := -I${PWD}/include ${DEP}

.DEFAULT_GOAL : all

all: ${OUT}/N2O r

${OUT}:; @mkdir $<

${OUT}/N2O:; agda -c --compile-dir=${OUT} $(GHC:%=--ghc-flag=%) ${SRC}/N2O.agda

r:; @${OUT}/N2O

c:; @find . -type f -name '*.agdai' -delete && rm -rf dist/

.PHONY: all r c
