DIR   := src/rewriting
PACK  := Rewriting
DEP   := Util Parsec
FILES := \
  context.ml \
  diagram.ml \
  elogic.ml \
  function.ml \
  monad.ml \
  parser.ml \
  position.ml \
  prelude.ml \
  rewrite.ml \
  rule.ml \
  signature.ml \
  substitution.ml \
  term.ml \
  trs.ml \
  variable.ml

include mk/subdir.mk
