import strutils, sequtils, strformat, sugar

import hmisc/types/seq2d
import hmisc/helpers

import hdrawing, hdrawing/term_buf
import trscore

# proc exprRepr*(vs: VarSym): string =
#   # if vs.listidxp:
#   #   "#" & $vs.idx
#   # else:
#   if vs.listvarp:
#     "@" & $vs.getVName()
#   else:
#     "_" & $vs.getVName()

func treeRepr*[V, F](term: Term[V, F],
                     cb: TermImpl[V, F], depth: int = 0): string =
  let ind = "  ".repeat(depth)
  case getKind(term):
    of tkConstant:
      return cb.valStrGen(getValue(term))
        .split("\n").mapIt(ind & "cst " & it).join("\n")
    of tkPlaceholder:
      return ind & "plh _"
    of tkVariable:
      return ind & "var " & getVName(term).exprRepr()
    of tkFunctor:
      return (
        @[ ind & "fun " & $(getFSym(term)) ] &
        getArguments(term).mapIt(treeRepr(it, cb, depth + 1))
      ).join("\n")
    of tkList:
      return (@[ ind & "lst"] & getElements(term).mapIt(
        treeRepr(it, cb, depth + 1))).join("\n")
    of tkPattern:
      &"{ind} <<<PATTERN TREE REPR>>>"

func treeRepr*[V, F](val: V, cb: TermImpl[V, F], depth: int = 0): string =
  let ind = "  ".repeat(depth)
  if cb.isFunctor(val):
    return (
      @[ ind & "fun " & $(cb.getSym(val)) ] &
      cb.getArguments(val).mapIt(treeRepr(it, cb, depth + 1))
    ).join("\n")
  else:
    return cb.valStrGen(val)
      .split("\n").mapIt(ind & "cst " & it).join("\n")

func exprRepr*[V, F](term: Term[V, F], cb: TermImpl[V, F]): string =
  case term.getKind():
    of tkPattern:
      term.getPatt().exprRepr(cb)
# func exprRepr*[V, F](expr: TermPattern[V, F], cb: TermImpl[V, F]): string =
      # raiseAssert("#[ IMPLEMENT ]#")
    of tkList:
      "[" & getElements(term).mapIt(exprRepr(it, cb)).join(", ") & "]"
    of tkConstant:
      if term.predp():
        "%?".toMagenta() & term.constPredRepr
      else:
        if term.functorvalp():
          $term.getFSym()
        else:
          "'" & cb.valStrGen(term.getValue()) & "'"
    of tkVariable:
      # debugecho term
      # tern(term.listvarp, "@", "_") &
        term.getVName().exprRepr()
    of tkFunctor:
      case term.headKind:
        of fhkValue:
          if ($getSym(term)).validIdentifier():
            $getSym(term) & "(" & term.getArguments().mapIt(
              it.exprRepr(cb)).join(", ") & ")"
          else:
            let subt = term.getArguments()
            case subt.len():
              of 1: &"{term.getSym()}({subt[0]})"
              of 2: &"{subt[0]} {term.getSym()} {subt[1]}"
              else:
                $term.getSym() & "(" & subt.mapIt(it.exprRepr(cb)).join(", ") & ")"

        of fhkPredicate:
          "%?".toMagenta() & term.funcPredRepr &
            term.bindvarp().tern(&"[{term.getVname().exprRepr()}]", "") &
            term.getArguments().mapIt(it.exprRepr(cb)).join(", ").wrap("()")
        else:
          raiseAssert("#[ IMPLEMENT ]#")

    of tkPlaceholder:
      "_"

func exprReprImpl*[V, F](matchers: MatcherList[V, F], cb: TermImpl): TermBuf
func exprRepr*[V, F](matcher: TermMatcher[V, F], cb: TermImpl[V, F]): TermBuf =
  let header = matcher.isPattern.tern(
    exprRepr(matcher.patt, cb), "func"
  ).toTermBufFast()
  # var tmp: Seq2D[TermBuf]
  # tmp.appendRow(@[

  # ], emptyTermBuf)

  var subvars: Seq2D[TermBuf]
  for varn, subp in matcher.subpatts:
    subvars.appendRow(
      @[
        (varn.exprRepr() & ": ").toTermBufFast(),
        subp.exprReprImpl(cb)
      ],
      emptyTermBuf
    )

  if subvars.len > 0:
    result = subvars.toTermBuf()
    result = @[@[header], @[result]].toTermBuf()
  else:
    result = header


func exprRepr*[V, F](env: TermEnv[V, F], cb: TermImpl[V, F], forceOneLine: bool = false): string =
  if env.len > 3 and not forceOneLine:
    "{\n" & env.mapPairs(&"  {lhs.exprRepr()} -> {rhs.exprRepr(cb)}").joinl() & "\n}"
  else:
    "{" & env.mapPairs(
      &"({lhs.exprRepr()} -> {rhs.exprRepr(cb)})"
    ).join(" ") & "}"

func exprReprImpl*[V, F](matchers: MatcherList[V, F], cb: TermImpl): TermBuf =
  var blocks: Seq2D[TermBuf]
  for idx, patt in matchers.patterns:
    let pref: string = if matchers.patterns.len == 1: "" else: $idx & ": "
    let bufs = @[pref.toTermBufFast(), patt.exprRepr(cb)]
    blocks.appendRow(bufs, emptyTermBuf)

  return blocks.toTermBuf()

func exprReprImpl*[V, F](rule: RulePair[V, F], cb: TermImpl[V, F]): seq[TermBuf] =
  let rhs: TermBuf = rule.gen.isPattern.tern(
    exprRepr(rule.gen.patt),
    "func"
  ).toTermBufFast()

  return @[ rule.matchers.exprReprImpl(cb), (" ~~> ").toTermBufFast(), rhs ]

func exprRepr*[V, F](rule: RulePair[V, F], cb: TermImpl[V, F]): string =
  @[exprReprImpl(rule, cb)].toTermBuf().toString()

func exprReprImpl*[V, F](sys: RedSystem[V, F], cb: TermImpl[V, F]): TermBuf =
  sys.mapPairs(
    @[ ($idx & ": ").toTermBufFast() ] & rhs.exprReprImpl(cb)
  ).toTermBuf()

func exprRepr*[V, F](sys: RedSystem[V, F], cb: TermImpl[V, F]): string =
  exprReprImpl(sys, cb).toString().split("\n").mapIt(
    it.strip(leading = false)).join("\n")

func exprRepr*[V, F](expr: TermPattern[V, F], cb: TermImpl[V, F]): string =
  case expr.kind:
    of tpkTerm:
      expr.term.getIt().exprRepr(cb)
    of tpkConcat:
      expr.patterns.mapIt(it.exprRepr(cb)).join(" & ").wrap("{}")
    of tpkAlternative:
      expr.patterns.mapIt(it.exprRepr(cb)).join(" | ").wrap("{}")
    of tpkZeroOrMore, tpkOptional, tpkNegation:
      let pref = case expr.kind:
        of tpkZeroOrMore: "*"
        of tpkOptional: "?"
        of tpkNegation: "!"
        else: ""

      pref & expr.patt.getIt().exprRepr(cb).wrap("()")
