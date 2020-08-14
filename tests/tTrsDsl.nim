import sugar, strutils, sequtils, strformat
import unittest

import tHtermsCallbackArithmetics
import tNimTrs

import ../src/nimtrs/[trscore, trsdsl]

suite "DSL":
  test "12":
    let term = mkOp(aopAdd, @[
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ]),
      mkOp(aopSucc, @[ mkOp(aopSucc, @[ mkVal(0) ]) ])
    ]).toTerm(arithmImpl)


    let trs = initTRS("aop", arithmImpl):
      Plus($a, 0) => $a
      Plus($a, Succ($b)) => Succ($a, $b)
      Mult($a, 0) => 0
      Mult($a, Succ($b)) => Plus($a, Mult($a, $b))
      _ => 0
