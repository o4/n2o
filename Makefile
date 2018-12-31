SRC := ${PWD}/n2o
OUT := ${PWD}/dist
DEP := n2o cereal network
GHC := -I${PWD}/include $(DEP:%=-package %)

.DEFAULT_GOAL : all

all: ${OUT}/N2O r

${OUT}:; @mkdir $<

${OUT}/N2O:; agda -c --compile-dir=${OUT} $(GHC:%=--ghc-flag=%) ${SRC}/N2O.agda

r:; @${OUT}/N2O

c:; @find . -type f -name '*.agdai' -delete && rm -rf dist/

.PHONY: all r c
