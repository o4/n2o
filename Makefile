SRC := ${PWD}/n2o
OUT := ${PWD}/dist
GHC := -I${PWD}/include

.DEFAULT_GOAL : all 

all: ${OUT}/N2O run

${OUT}:; @mkdir $<

${OUT}/N2O:; @agda -c --compile-dir=${OUT} $(GHC:%=--ghc-flag=%) ${SRC}/N2O.agda

run:; @${OUT}/N2O

clean:; @find . -type f -name '*.agdai' -delete 

.PHONY: dist all run clean
