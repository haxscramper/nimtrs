import hmisc/helpers
import nimtrs/[trscore, trspprint, trsdsl]
import sequtils, strformat, strutils, macros
import hmisc/algo/halgorithm
import hmisc/types/[hnim_ast, colorstring]
import unittest, sets, options

import hpprint, hpprint/hpprint_repr

import ast_term


template transformTest*(body: untyped, termIn, termOut: typed): untyped =
  let termIn1 = termIn.toTerm(astImpl)
  let termRes = matchWith(termIn1, astImpl):
    body

  echo "input___: ", termIn1.exprRepr(astImpl)
  echo "expected: ", termOut.toTerm(astImpl).exprRepr(astImpl)
  if termRes.isSome():
    let res = termRes.get().fromTerm(astImpl)
    cmpTerm res, termOut
  else:
    fail("Rewrite is none")


suite "Hterms ast rewriting":
  test "Ast rewriting":
    let rSystem = makeReductionSystem(@[
      makeRulePair(
        nOp(akCall, @[
          mkIdent("someFunc").nConst(), mkVal(9000).nConst()
        ]).makeMatcher(),
        nConst(mkLit("Hello 9000")).makeGenerator()
    )])

    let obj =  mkOp(akCall, @[ mkIdent("someFunc"), mkVal(9000) ])
    let res = reduce(obj.toTerm(astImpl), rSystem)
    if res.ok:
      let resAst = res.term.fromTerm(astImpl)
      echo resAst
      assert resAst == Ast(kind: akStrLit, strVal: "Hello 9000")
    else:
      fail()
      echo res.term.treeRepr(astImpl)

  test "Pattern rewriting with value genertion via external function":

    let inval = mkCond(mkCall("==", mkLit("999"), mkLit("999")))

    if inval.matchPattern(astImpl, Condition(Call(*@a))):
      echo a.objTreeRepr().treeRepr()

    transformTest do:
      Condition(Call(%!mkIdent("=="), $a, $a)) => %!mkLit(1)
    do:
      inval
    do:
      mkLit(1)

  test "Pattern matching with predicates; functor head":
    func isCond(f: AstKind): bool = (f == akCondition)

    transformTest do:
      %?isCond(Call($a, *_)) => $a
    do:
      mkCond(mkCall("<", mkLit(900), mkLit(100)))
    do:
      mkIdent("<")

  test "Pattern matching with predicates; constant value":
    func isComp(v: Ast): bool =
      (v.kind == akIdent) and (v.strVal in ["<", ">", ">=", "<=", "=="])

    transformTest do:
      Condition(Call(%?isComp, $a, $b)) => $a
    do:
      mkCond(mkCall("<", mkLit(100), mkLit(200)))
    do:
      mkLit(100)

  test "Pattern matching; copy functor head":
    transformTest do:
      [$head](Call(*_)) => [$head](%!mkCall("+", mkLit(1)))
    do:
      mkCond(mkCall("!", mkLit(100)))
    do:
      mkCond(mkCall("+", mkLit(1)))

  test "Pattern matching; splice functor arguments":
    transformTest do:
      Condition(Call(*@b)) => Call(@b)
    do:
      mkCond(mkCall("&", mkLit(100)))
    do:
      mkCall("&", mkLit(100))

  test "Pattern matching; negation":
    ## Capture all arguments
    # TODO IMPLEMENT
    when false:
      transformTest do:
        Condition(Call(
          *(!%!mkLit(100) & @a) & !%!mkLit(100) & *_
        )) => Call(@b)
      do:
        mkCond(mkCall(mkLit(12), mkLit(1223), mkLit(100), mkLit(99)))
      do:
        mkCond(mkCall(mkLit(12), mkLit(1223)))


  test "Pattern matching; interpolation of the arguments":
    # TODO IMPLEMENT
    let
      funcHead = akCall
      replaceVal = mkLit(2 + 4 #[ some crazy computations to get the vale]#)

    when false:
      transformTest do:
        Condition(Call(`mkLit(100)`)) => `funcHead`(`replaceVal`)
      do:
        mkCond(mkCall(mkLit(100)))
      do:
        mkCond(mkCall(replaceVal))
