import hmisc/helpers
import hnimast
import nimtrs/[trscore, trspprint, trsdsl]
import sequtils, strformat, strutils, macros
import hmisc/algo/halgorithm
import hmisc/types/colorstring
import unittest, sets, options

import hpprint, hpprint/hpprint_repr

type
  AstKind* = enum
    # Constant values
    akStrLit
    akIntLit
    akIdent

    # Functors
    akCall
    akCondition

  Ast* = object
    case kind*: AstKind
      of akStrLit, akIdent:
        strVal*: string
      of akIntLit:
        intVal*: int
      else:
        subnodes*: seq[Ast]

proc `==`*(lhs, rhs: Ast): bool =
  lhs.kind == rhs.kind and
  (
    case lhs.kind:
      of akStrLit, akIdent: lhs.strVal == rhs.strVal
      of akIntLit: lhs.intVal == rhs.intVal
      else: subnodesEq(lhs, rhs, subnodes)
  )

type AstTerm* = Term[Ast, AstKind]
func nOp*(op: AstKind, subt: seq[AstTerm]): AstTerm =
  case op:
    of akStrLit .. akIdent:
      assert false
    else:
      return makeFunctor[Ast, AstKind](op, subt)

func nVar*(n: string): AstTerm =
  makeVariable[Ast, AstKind](n)

func mkOp*(op: AstKind, sub: seq[Ast]): Ast =
  case op:
    of akCall, akCondition:
      Ast(kind: op, subnodes: sub)
    else:
      raiseAssert("12")

func objTreeRepr*(a: Ast): ObjTree =
  case a.kind:
    of akIntLit:
      pptConst($a.intVal)
    of akStrLit:
      pptConst(a.strVal)
    of akIdent:
      pptObj("ident", pptConst(a.strVal))
    else:
      pptObj($a.kind, a.subnodes.mapIt(it.objTreeRepr()))

func objTreeRepr*(a: seq[Ast]): ObjTree =
  a.mapIt(it.objTreeRepr()).pptSeq()

func mkVal*(val: int): Ast = Ast(kind: akIntLit, intVal: val)
func mkIdent*(val: string): Ast = Ast(kind: akIdent, strVal: val)
func mkLit*(val: string): Ast = Ast(kind: akStrLit, strVal: val)
func mkLit*(val: int): Ast = Ast(kind: akIntLit, intVal: val)
func nConst*(n: Ast): AstTerm = makeConstant(n, n.kind)
func mkCond*(a: Ast): Ast = Ast(kind: akCondition, subnodes: @[a])
func mkCall*(n: string, args: varargs[Ast]): Ast =
  Ast(kind: akCall,
      subnodes: @[mkIdent(n)] & args.mapIt(it))

func exprRepr*(a: Ast): string =
  let color = not defined(plainStdout)
  case a.kind:
    of akIntLit:
      ($a.intVal).toCyan(color)
    of akStrLit:
      a.strVal.toYellow(color)
    of akIdent:
      a.strVal.toGreen(color)
    else:
      a.subnodes.mapIt(it.exprRepr()).join(", ").wrap("[ ]")

let astImpl* = TermImpl[Ast, AstKind](
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

proc exprRepr*(a: AstTerm |
              TermPattern[Ast, AstKind] |
              TermEnv[Ast, AstKind]
             ): string = exprRepr(a, astImpl)
proc exprRepr(elems: seq[AstTerm]): string =
  elems.mapIt(it.exprRepr(astImpl)).join(", ").wrap(("[", "]"))


proc cmpTerm*(term: AstTerm | Ast, val: Ast | AstTerm): void =
  let ok =
    (when term is AstTerm: term.fromTerm() else: term) ==
    (when val is AstTerm: val.fromTerm() else: val)

  if not ok:
    echo "Found:"
    echo treeRepr(term, astImpl)
    echo "Expected:"
    echo treeRepr(val, astImpl)
    raiseAssert("Fail")

func toTerm*(val: int, impl: TermImpl[Ast, AstKind]): AstTerm =
  toTerm(mkVal(val), impl)
