import sugar, strutils, sequtils, strformat, macros
import unittest
import strutils, sequtils, strformat, sugar, options, sets

import tHtermsCallbackArithmetics
import tNimTrs

import hmisc/algo/[halgorithm, hseq_mapping]
import ../src/nimtrs/[trscore, trsdsl, nimast_trs]
import hpprint/objdiff

func toTerm*(val: int, impl: TermImpl[Arithm, ArithmOp]): ATerm =
  nConst(val)


suite "DSL":
  test "12":
    let term = mkOp(aopAdd, @[
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ]),
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ])
    ]).toTerm(arithmImpl)

    when false: # NOTE compilation ERROR test
      discard initTRS(arithmImpl):
        Add($a, 0) => Succ(@a)

    when false: # NOTE compilation ERROR test
      discard initTRS(arithmImpl):
        Add($a, 0) => Succ($a, $b)

    when true:
      let trs = initTRS(arithmImpl):
        Add($a, 0) => $a
        Add($a, Succ($b)) => Succ(Add($a, $b))
        Mult($a, 0) => 0
        Mult($a, Succ($b)) => Add($a, Mult($a, $b))


      echo term.fromTerm(arithmImpl)
      let res = term.reduce(trs, reduceConstraints = rcNoConstraints)
      echo $res[0].fromTerm(arithmImpl)

  test "Use in macro":
    template matchPatternNim(term: NodeTerm, patt: untyped): untyped =
      matchPattern(term, nimAstImpl, patt)

    macro ifTest(body: untyped): untyped =
      for stmt in body:
        # echo stmt.treeRepr()
        let term = stmt.toTerm(nimAstImpl)
        if term.matchPatternNim(
          IfStmt(*ElifBranch(@conds, @bodies) & ?Else($elsebody))):

          assert conds is seq[NimNode]
          assert bodies is seq[NimNode]
          assert elsebody is Option[NimNode]

          if elsebody.isSome():
            assert conds.len == 2
            assert bodies.len == 2
          else:
            assert conds.len == 1
        else:
          echo "does not match"

      when false: # this is a TEST for compilation error
        if term.matchPatternNim(IfStmt($hello, @hello)):
          discard

    ifTest:
      if 12 == 22:
        echo "123"
      elif false:
        echo "123"
      else:
        echo "123123"

    ifTest:
      if 20 == 29:
        echo "123"
