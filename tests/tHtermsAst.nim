import hmisc/helpers
import nimtrs/[trscore, trspprint, trsdsl]
import sequtils, strformat, strutils
import hmisc/algo/halgorithm
import hmisc/types/hnim_ast
import unittest, sets, options

import hpprint, hpprint/hpprint_repr

type
  AstKind = enum
    # Constant values
    akStrLit
    akIntLit
    akIdent

    # Functors
    akCall
    akCondition

  Ast = object
    case kind: AstKind
      of akStrLit, akIdent:
        strVal: string
      of akIntLit:
        intVal: int
      else:
        subnodes: seq[Ast]

proc `==`(lhs, rhs: Ast): bool =
  lhs.kind == rhs.kind and
  (
    case lhs.kind:
      of akStrLit, akIdent: lhs.strVal == rhs.strVal
      of akIntLit: lhs.intVal == rhs.intVal
      else: subnodesEq(lhs, rhs, subnodes)
  )

type AstTerm = Term[Ast, AstKind]
func nOp(op: AstKind, subt: seq[AstTerm]): AstTerm =
  case op:
    of akStrLit .. akIdent:
      assert false
    else:
      return makeFunctor[Ast, AstKind](op, subt)

func nVar(n: string): AstTerm =
  makeVariable[Ast, AstKind](n)

func mkOp(op: AstKind, sub: seq[Ast]): Ast =
  case op:
    of akCall, akCondition:
      Ast(kind: op, subnodes: sub)
    else:
      raiseAssert("12")

func objTreeRepr(a: Ast): ObjTree = discard
  # case a.kind:
  #   of akIntLit:

func mkVal(val: int): Ast = Ast(kind: akIntLit, intVal: val)
func mkIdent(val: string): Ast = Ast(kind: akIdent, strVal: val)
func mkLit(val: string): Ast = Ast(kind: akStrLit, strVal: val)
func mkLit(val: int): Ast = Ast(kind: akIntLit, intVal: val)
func nConst(n: Ast): AstTerm = makeConstant(n, n.kind)
func mkCond(a: Ast): Ast = Ast(kind: akCondition, subnodes: @[a])
func mkCall(n: string, args: varargs[Ast]): Ast =
  Ast(kind: akCall,
      subnodes: @[mkIdent(n)] & args.mapIt(it))


let cb = TermImpl[Ast, AstKind](
  getSym: (proc(n: Ast): AstKind = n.kind),
  isFunctorSym: (proc(kind: AstKind): bool = kind in {akCall .. akCondition}),
  makeFunctor: (
    proc(op: AstKind, sub: seq[Ast]): Ast =
      result = Ast(kind: op); result.subnodes = sub
  ),
  getArguments: (proc(n: Ast): seq[Ast] = n.subnodes),
  # setSubt: (proc(n: var Ast, sub: seq[Ast]) = n.subnodes = sub),
  valStrGen: (proc(n: Ast): string = "[[ TODO ]]"),
)


proc cmpTerm*(term: AstTerm | Ast, val: Ast | AstTerm): void =
  let ok =
    (when term is AstTerm: term.fromTerm() else: term) ==
    (when val is AstTerm: val.fromTerm() else: val)

  if not ok:
    echo "Found:"
    echo treeRepr(term, cb)
    echo "Expected:"
    echo treeRepr(val, cb)
    raiseAssert("Fail")

template transformTest*(body: untyped, termIn, termOut: typed): untyped =
  static:
    echo astToStr(body)
    echo astToStr(termIn)

  let termIn1 = termIn.toTerm(cb)
  let termRes = matchWith(termIn1, cb):
    body

  if termRes.isSome():
    let res = termRes.get().fromTerm(cb)
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
    let res = reduce(obj.toTerm(cb), rSystem)
    if res.ok:
      let resAst = res.term.fromTerm(cb)
      echo resAst
      assert resAst == Ast(kind: akStrLit, strVal: "Hello 9000")
    else:
      fail()
      echo res.term.treeRepr(cb)

  test "Pattern rewriting":
    func toTerm(val: int, impl: TermImpl[Ast, AstKind]): AstTerm =
      toTerm(mkVal(val), impl)

    let inval = mkCond(mkCall("==", mkLit("999"), mkLit("999")))

    if inval.matchPattern(cb, Condition($a)):
      echo a.objTreeRepr().treeRepr()

    transformTest do:
      Condition(Call(%!mkIdent("=="), $a, $a)) => IntLit(1)
    do:
      inval
    do:
      mkLit(1)
