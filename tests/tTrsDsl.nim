import sugar, strutils, sequtils, strformat, macros
import unittest
import strutils, sequtils, strformat, sugar, options, sets

import tHtermsCallbackArithmetics
import tNimTrs

import hmisc/algo/[halgorithm, hseq_mapping]
import ../src/nimtrs/[trscore, trsdsl, nimast_trs]
import hpprint/objdiff

func toTerm*(impl: TermImpl[Arithm, ArithmOp], val: int): ATerm =
  nConst(val)

suite "DSL":
  test "12":
    let term = mkOp(aopAdd, @[
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ]),
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ])
    ]).toTerm(arithmImpl)

    when false:
      let trs = initTRS("aop", arithmImpl):
        Add($a, 0) => $a
        Add($a, Succ($b)) => Succ(Add($a, $b))
        Mult($a, 0) => 0
        Mult($a, Succ($b)) => Add($a, Mult($a, $b))


      echo term.fromTerm(arithmImpl)
      let res = term.reduce(trs, reduceConstraints = rcNoConstraints)
      echo $res[0].fromTerm(arithmImpl)

  test "Use in macro":
    template matchPatternNim(term: NodeTerm, patt: untyped): untyped =
      matchPattern(term, "nnk", nimAstImpl, patt)

    macro ifTest(body: untyped): untyped =
      static: echo "iftest macro"
      for stmt in body:
        let term = stmt.toTerm(nimAstImpl)
        if term.matchPatternNim(
          IfStmt(*ElifBranch(@conds, @bodies) & ?Else(elsebody))):

          assert conds is seq[NimNode]
          assert bodies is seq[NimNode]
          assert elsebody is NimNode

    ifTest:
      if 12 == 22:
        echo "123"
      else:
        echo "123123"
