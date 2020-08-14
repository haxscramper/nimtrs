import macros, strformat, sets, sugar
import trscore
import hmisc/[hexceptions, helpers]
import hmisc/types/[colorstring, initcalls]


type
  GenParams = object
    vName, fName, fPrefix, termId, implId: string
    # vName: string
    # fName: string
    # fPrefix: string
    # termId: string
    # implId: string

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
          var varset: VarSet
          let args = collect(newSeq):
            for arg in body[1..^1]:
              let (body, vars) = parseTermPattern(arg, conf)
              varset.incl vars # TODO check if variables don't
                               # override each other
              body

          result[0] = mkCallNode("makeFunctor", @[
            ident(conf.fPrefix & id)] & args, @[vType, fType])
          result[1] = varset


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
      case body[0].strVal():
        of "$", "@":
          let vsym = makeVarSym(
            body[1].strVal(), islist = (body[0].strval() == "@"))
          result[0] = mkCallNode(
            "makeVariable", [vType, fType], makeInitAllFields(vsym))
          result[1].incl vsym
        else:
          raiseAssert(&"#[ IMPLEMENT {body[0].strVal()} ]#")
    of nnkIntLit:
      result[0] = mkCallNode("toTerm", @[ident(conf.implId), body])
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

macro initTRS*(fPrefix: string, impl: typed, body: untyped): untyped =
  # TODO infer `fPrefix` from functor symbol
  impl.expectNode(nnkSym, mkNType("TermImpl", @["V", "F"]))
  assertNodeIt(
    fPrefix,
    fPrefix.kind in {nnkStrLit, nnkIdent},
    "Expected string literal or ident for functor prefix")

  let implType = impl.getTypeInst()
  result = initTRSImpl(GenParams(
    vName: implType[1].strVal(),
    fName: implType[2].strVal(),
    fPrefix: fPrefix.strVal(),
    implId: impl.strVal()
  ), body)

  colorPrint(result)
