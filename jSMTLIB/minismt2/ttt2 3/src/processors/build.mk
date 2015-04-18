DIR    := src/processors
PACK   := Processors
DEP    := Util Rewriting Automata Logic Parsec
FILES  := \
  logic/arcticCoefficient.ml \
  logic/boolCoefficient.ml \
  logic/coefficient.ml \
  logic/countCoefficient.ml \
  modifier/restore.ml \
  xmlOutput.ml \
  rewriting/context.ml \
  rewriting/monad.ml \
  rewriting/prelude.ml \
  rewriting/filtering.ml \
  rewriting/rewritingx.ml \
  rewriting/label.ml \
  rewriting/rule.ml \
  rewriting/trs.ml \
  rewriting/projection.ml \
  rewriting/position.ml \
  rewriting/substitution.ml \
  rewriting/signature.ml \
  rewriting/graph.ml \
  rewriting/diagram.ml \
  rewriting/sequence.ml \
  rewriting/term.ml \
  confluence/kleinHirokawa.ml \
  confluence/aotoToyama.ml \
  confluence/ruleLabeling.ml \
  confluence/nonconfluence.ml \
  confluence/closed.ml \
  confluence/decreasing.ml \
  confluence/shift.ml \
  confluence/groundCR.ml \
  predicate/isDuplicating.ml \
  predicate/isWcr.ml \
  predicate/isOutermost.ml \
  predicate/isSrs.ml \
  predicate/isLeftGround.ml \
  predicate/isGround.ml \
  predicate/isRightLinear.ml \
  predicate/isOverlapping.ml \
  predicate/isShallow.ml \
  predicate/isTrs.ml \
  predicate/isFlat.ml \
  predicate/isDummy.ml \
  predicate/isApplicative.ml \
  predicate/isLinear.ml \
  predicate/isStandard.ml \
  predicate/isRelative.ml \
  predicate/isErasing.ml \
  predicate/isInnermost.ml \
  predicate/isRightGround.ml \
  predicate/isLeftLinear.ml \
  predicate/isOverlay.ml \
  predicate/isFull.ml \
  predicate/isStronglyNonOverlapping.ml \
  predicate/isCollapsing.ml \
  predicate/isConstructor.ml \
  nontermination/loop.ml \
  nontermination/loopSat.ml \
  nontermination/redexProblem.ml \
  nontermination/unfolding.ml \
  nontermination/variables.ml \
  nontermination/contained.ml \
  transformation/uncurry.ml \
  transformation/labeling/rootLabeling.ml \
  transformation/labeling/quasiRootLabeling.ml \
  transformation/ur.ml \
  transformation/uncurryx.ml \
  transformation/cr.ml \
  transformation/dpify.ml \
  transformation/emb.ml \
  transformation/rt.ml \
  transformation/sorted.ml \
  transformation/split.ml \
  transformation/commute.ml \
  transformation/reflect.ml \
  transformation/cp.ml \
  transformation/reverse.ml \
  transformation/linear.ml \
  transformation/typeIntroduction.ml \
  transformation/st.ml \
  problem.ml \
  result.ml \
  termination/dg/edg.ml \
  termination/dg/dg.ml \
  termination/dg/tdg.ml \
  termination/dg/cdg.ml \
  termination/dg/adg.ml \
  termination/labeling/semanticLabeling.ml \
  termination/subtermCriterion.ml \
  termination/dp.ml \
  termination/sizeChangeTermination.ml \
  termination/interpretations/domain.ml \
  termination/interpretations/interpretation.ml \
  termination/interpretations/arcticInterpretation.ml \
  termination/interpretations/polynomial.ml \
  termination/interpretations/matrix.ml \
  termination/interpretations/monomial.ml \
  termination/interpretations/polynomialInterpretation.ml \
  termination/interpretations/matrixInterpretation.ml \
  termination/interpretations/ordinalInterpretation.ml \
  termination/interpretations/ordinal.ml \
  termination/interpretations/higherOrdinalInterpretation.ml \
  termination/interpretations/fixedBaseElementaryInterpretation.ml \
  termination/interpretations/fixedBaseElementary.ml \
  termination/bounds/categorization.ml \
  termination/bounds/enrichment.ml \
  termination/bounds/bounds.ml \
  termination/bounds/automatax.ml \
  termination/cfs.ml \
  termination/orderings/kbo.ml \
  termination/orderings/tkbo.ml \
  termination/orderings/lpo.ml \
  termination/orderings/weights.ml \
  termination/orderings/precedence.ml \
  termination/sccs.ml termination/trivial.ml


include mk/subdir.mk
