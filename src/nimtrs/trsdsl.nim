import macros, strformat, sets, sugar, strutils, sequtils
import trscore
import hmisc/[hexceptions, helpers]
import hmisc/types/[colorstring, initcalls]

type
  GenParams = object
    vName, fName, fPrefix, termId, implId: string

template mapItInfix*(topInfix: NimNode, op: untyped): untyped =
  type ResT = typeof((var it {.inject.}: NimNode; op))
  var curr = topInfix
  # let it {.inject.} = topInfix
  var res: seq[ResT]

  if curr.kind == nnkInfix:
    block:
      let it {.inject.} = curr[1]
      res.add op

    let infix = topInfix[0].strVal()
    # var cnt = 0
    while curr.kind == nnkInfix and curr[0] == ident(infix):
      let it {.inject.} = curr[2]
      res.add op
      curr = curr[1]

      # inc cnt
      # if cnt > 3:
      #   quit 0

    # let it {.inject.} = curr
    # res.add op
    # res.reverse

  res

func parseTermPattern(body: NimNode, conf: GenParams): (NimNode, VarSet) =
  let
    fType = mkNType(conf.fName)
    vType = mkNType(conf.vName)

  case body.kind:
    of nnkCall:
      case body[0].kind:
        of nnkAccQuoted:
          raiseAssert("#[ IMPLEMENT ]#")
        of nnkIdent:
          let id = body[0].strVal()
          let args = collect(newSeq):
            for arg in body[1..^1]:
              let (body, vars) = parseTermPattern(arg, conf)
              result[1].incl vars # TODO check if variables don't
                                  # override each other
              body

          result[0] = mkCallNode("makeFunctor", @[
            ident(conf.fPrefix & id)] &
              args.mapIt(newCall("makePattern", it)), @[vType, fType])


        else:
          raiseAssert(&"#[ IMPLEMENT for kind {body[0].kind} ]#")

    of nnkIdent:
      let str = body.strVal()
      if str == "_":
        result[0] = mkCallNode("makePlaceholder", [vType, fType])
      else:
        let vsym = parseVarSym(str)
        result[0] = mkCallNode("makeVariable", [vType, fType],
                               makeInitAllFields(vsym))

        result[1].incl vsym
    of nnkPrefix:
      # echov body.treeRepr()
      case body[0].strVal():
        of "$", "@":
          let vsym = makeVarSym(
            body[1].strVal(), islist = (body[0].strval() == "@"))
          # echov vsym
          result[0] = mkCallNode(
            "makeVariable", [vType, fType], makeInitAllFields(vsym))
          result[1].incl vsym
        of "*", "?", "+", "!":
          case body[0].kind:
            of nnkPar:
              assertNodeIt(body[0], body[0].len == 1,
                           "Use `&` for concatenation, not commas")

              result = body[0][0].parseTermPattern(conf)
            else:
              result = body[1].parseTermPattern(conf)

          let callname =
            case body[0].strVal():
              of "*": "makeZeroOrMoreP"
              of "+": "makeOneOrMoreP"
              of "?": "makeOptP"
              of "!": "makeNegationP"
              else: "<<<INVALID_PREFIX>>>"

          result[0] = mkCallNode(callname, @[result[0]])
        else:
          raiseAssert(&"#[ IMPLEMENT {body[0].strVal()} ]#")
    of nnkIntLit:
      result[0] = mkCallNode("toTerm", @[ident(conf.implId), body])
    of nnkInfix:
      case body[0].strVal():
        of "&", "|":
          let elems: seq[NimNode] = body.mapItInfix:
            let (body, newvars) = it.parseTermPattern(conf)
            result[1].incl newvars
            body

          let callname =
            case body[0].strVal():
              of "&": "makeAndP"
              of "|": "makeOrP"
              else: "<<<INVALID_PREFIX>>>"

          result[0] = mkCallNode(callname, @[ elems.toBracketSeq() ])
    else:
      raiseAssert(&"#[ IMPLEMENT for kind {body.kind} ]#")


func parseTermExpr(body: NimNode, conf: GenParams, vars: VarSet): NimNode =
  let (impl, vars) = parseTermPattern(body, conf)
  return impl

func initTRSImpl*(conf: GenParams, body: NimNode): NimNode =
  # TODO: generate static assertion for match arms to have the same
  # result type. IDEA: Rewrite let side in form of `let res = <expr>;
  # static: assert expr is <restype>`.

  # TODO in order to implement this I have to somehow store
  # `CodeError` exception in generated code (in order to provide
  # better error message).
  result = newCall("makeReductionSystem")
  for idx, line in body:
    assertNodeIt(
      line,
      (line.kind == nnkInfix and line[0].strVal == "=>"),
      msgjoin("Expected match arm in form of",
              "`<pattern> => <result>`".toYellow()))

    # if line[1] == ident("_"):
    #   var novars: HashSet[VarSym]
    #   result.add nnkElse.newTree(
    #     parseTermExpr(line[2], conf, novars)
    #   )
    # else:
    let (matcher, vars) =  parseTermPattern(line[1], conf)
    let generator = parseTermExpr(line[2], conf, vars)
    result.add newCall("makeRulePair",
                       newCall("makeMatcher", matcher),
                       newCall("makeGenerator", generator))


  # echov result.toStrLit()


func expectNode*(node: NimNode, kind: NimNodeKind, stype: NType): void =
  assertNodeIt(
      node,
      (node.kind == nnkSym and
       node.getTypeInst().kind == nnkBracketExpr and
       node.getTypeInst()[0].strVal() == stype.head),
      msgjoin(
        "Expected variable of type `", stype, "` but found '",
        node.toStrLit().strVal().toYellow(), "' of type",
        node.getTypeInst().toStrLit().strVal().toYellow()
    ))

proc pprintCalls*(node: NimNode, level: int): void =
  let pref = "  ".repeat(level)
  let pprintKinds = {nnkCall, nnkPrefix, nnkBracket}
  case node.kind:
    of nnkCall:
      echo pref, $node[0].toStrLit()
      if node[1..^1].noneOfIt(it.kind in pprintKinds):
        echo pref, node[1..^1].mapIt($it.toStrLit()).join(", ").toYellow()
      else:
        for arg in node[1..^1]:
          pprintCalls(arg, level + 1)
    of nnkPrefix:
      echo pref, node[0]
      pprintCalls(node[1], level)
    of nnkBracket:
      for subn in node:
        pprintCalls(subn, level + 1)
    of nnkIdent:
      echo pref, ($node).toGreen()
    else:
      echo ($node.toStrLit()).indent(level * 2)

func makeGenParams*(fPrefix, impl: NimNode): GenParams =
  impl.expectNode(nnkSym, mkNType("TermImpl", @["V", "F"]))
  assertNodeIt(
    fPrefix,
    fPrefix.kind in {nnkStrLit, nnkIdent},
    "Expected string literal or ident for functor prefix")

  let implType = impl.getTypeInst()
  result = GenParams(
     vName: implType[1].strVal(),
     fName: implType[2].strVal(),
     fPrefix: fPrefix.strVal(),
     implId: impl.strVal()
   )

macro initTRS*(fPrefix: string, impl: typed, body: untyped): untyped =
  result = initTRSImpl(makeGenParams(fPrefix, impl) , body)


macro matchPattern*[V, F](
  term: Term[V, F], fPrefix: string, impl: TermImpl[V, F],
  patt: untyped): untyped =
  let conf = makeGenParams(fPrefix, impl)
  let (patt, vars) = patt.parseTermPattern(conf)
  # patt.pprintCalls(0)
  # echo patt.toStrLit()
  # echo vars
  let unifcall = newCall("unifp", term, patt)
  var
    vardecls: seq[NimNode]
    varassign: seq[NimNode]

  let
    vtype = ident(conf.vName)

  for varsym in vars:
    let
      varid = ident(varsym.getvname)
      varn = newLit(varsym.getvname)

    vardecls.add:
      if varsym.listvarp:
        quote do:
           var `varid` {.inject.}: seq[`vtype`]
      else:
        quote do:
          var `varid` {.inject.}: `vtype`

    varassign.add:
      if varsym.listvarp:
        quote do:
          `varid` = env.getValues(makeVarSym(`varn`, true), `impl`)
      else:
        quote do:
          `varid` = env[makeVarSym(`varn`, false)].fromTerm(`impl`)

  block:
    let vardecls = newStmtList(vardecls)
    let varassign = newStmtList(varassign)
    result = quote do:
      `vardecls`
      if `unifcall`:
        `varassign`
        true
      else:
        false

  # echo result.toStrLit()
