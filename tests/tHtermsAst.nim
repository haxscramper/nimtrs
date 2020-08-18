import hmisc/helpers
import nimtrs/[trscore, trspprint, trsdsl]
import sequtils, strformat, strutils, macros
import hmisc/algo/halgorithm
import hmisc/types/[hnim_ast, colorstring]
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

func objTreeRepr(a: Ast): ObjTree =
  case a.kind:
    of akIntLit:
      pptConst($a.intVal)
    of akStrLit:
      pptConst(a.strVal)
    of akIdent:
      pptObj("ident", pptConst(a.strVal))
    else:
      pptObj($a.kind, a.subnodes.mapIt(it.objTreeRepr()))

func objTreeRepr(a: seq[Ast]): ObjTree =
  a.mapIt(it.objTreeRepr()).pptSeq()

func mkVal(val: int): Ast = Ast(kind: akIntLit, intVal: val)
func mkIdent(val: string): Ast = Ast(kind: akIdent, strVal: val)
func mkLit(val: string): Ast = Ast(kind: akStrLit, strVal: val)
func mkLit(val: int): Ast = Ast(kind: akIntLit, intVal: val)
func nConst(n: Ast): AstTerm = makeConstant(n, n.kind)
func mkCond(a: Ast): Ast = Ast(kind: akCondition, subnodes: @[a])
func mkCall(n: string, args: varargs[Ast]): Ast =
  Ast(kind: akCall,
      subnodes: @[mkIdent(n)] & args.mapIt(it))

func exprRepr(a: Ast): string =
  case a.kind:
    of akIntLit:
      ($a.intVal).toCyan()
    of akStrLit:
      a.strVal.toYellow()
    of akIdent:
      a.strVal.toGreen()
    else:
      a.subnodes.mapIt(it.exprRepr()).join(", ").wrap("[ ]")

let cb = TermImpl[Ast, AstKind](
  getSym: (proc(n: Ast): AstKind = n.kind),
  isFunctorSym: (
    proc(kind: AstKind): bool =
      result = kind in {akCall .. akCondition}
      # debugecho "Kind is functor? ", kind, ": ", result
  ),
  makeFunctor: (
    proc(op: AstKind, sub: seq[Ast]): Ast =
      # debugecho "making functor for kind ", op
      result = Ast(kind: op)
      result.subnodes = sub
  ),
  getArguments: (proc(n: Ast): seq[Ast] = n.subnodes),
  # setSubt: (proc(n: var Ast, sub: seq[Ast]) = n.subnodes = sub),
  valStrGen: (proc(n: Ast): string = n.exprRepr()),
)

proc exprRepr(a: AstTerm |
              TermPattern[Ast, AstKind] |
              TermEnv[Ast, AstKind]
             ): string = exprRepr(a, cb)
proc exprRepr(elems: seq[AstTerm]): string =
  elems.mapIt(it.exprRepr(cb)).join(", ").wrap(("[", "]"))


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

func toTerm(val: int, impl: TermImpl[Ast, AstKind]): AstTerm =
  toTerm(mkVal(val), impl)


template transformTest*(body: untyped, termIn, termOut: typed): untyped =
  let termIn1 = termIn.toTerm(cb)
  let termRes = matchWith(termIn1, cb):
    body

  if termRes.isSome():
    let res = termRes.get().fromTerm(cb)
    cmpTerm res, termOut
  else:
    echo "input:\n", termIn1.exprRepr(cb)
    echo "expected:\n", termOut.toTerm(cb).exprRepr(cb)
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

  test "Pattern rewriting with value genertion via external function":

    let inval = mkCond(mkCall("==", mkLit("999"), mkLit("999")))

    if inval.matchPattern(cb, Condition(Call(*@a))):
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
