import sugar, strutils, sequtils, strformat
import unittest
import strutils, sequtils, strformat, sugar, options, sets

import tHtermsCallbackArithmetics
import tNimTrs

import hmisc/algo/[halgorithm, hseq_mapping]
import ../src/nimtrs/[trscore, trsdsl]

func toTerm*(impl: TermImpl[Arithm, ArithmOp], val: int): ATerm =
  nConst(val)

suite "DSL":
  test "12":
    let term = mkOp(aopAdd, @[
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ]),
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ])
    ]).toTerm(arithmImpl)

    let trs = initTRS("aop", arithmImpl):
      Add($a, 0) => $a
      Add($a, Succ($b)) => Succ($a, $b)
      Mult($a, 0) => 0
      Mult($a, Succ($b)) => Add($a, Mult($a, $b))

    echo term.fromTerm(arithmImpl)
    let res = term.reduce(trs, reduceConstraints = rcNoConstraints)
    echo $res[0].fromTerm(arithmImpl)
