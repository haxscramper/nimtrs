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
  echov body.treeRepr()

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

          result[0] = mkCallNode("makeFunctor", args, @[vType, fType])
          result[1] = varset


        else:
          raiseAssert(&"#[ IMPLEMENT for kind {body[0].kind} ]#")

    of nnkIdent:
      let vsym = parseVarSym(body.strVal())
      result[0] = mkCallNode("makeVariable", [vType, fType], newLit(vsym))

      result[1].incl vsym
    of nnkPrefix:
      case body[0].strVal():
        of "$", "@":
          let vsym = makeVarSym(
            body[1].strVal(), islist = (body[0].strval() == "@"))
          result[0] = mkCallNode(
            "makeVariable", [vType, fType], newLit(vsym))
          result[1].incl vsym
        else:
          raiseAssert("#[ IMPLEMENT ]#")
    # of nnkIntLit:
    else:
      raiseAssert(&"#[ IMPLEMENT for kind {body.kind} ]#")


func parseTermExpr(body: NimNode, conf: GenParams, vars: VarSet): NimNode =
  discard

func initTRSImpl*(conf: GenParams, body: NimNode): NimNode =
  # TODO: generate static assertion for match arms to have the same
  # result type. IDEA: Rewrite let side in form of `let res = <expr>;
  # static: assert expr is <restype>`.

  # TODO in order to implement this I have to somehow store
  # `CodeError` exception in generated code (in order to provide
  # better error message).
  result = nnkIfStmt.newTree()
  for idx, line in body:
    assertNodeIt(
      line,
      (line.kind == nnkInfix and line[0].strVal == "=>"),
      msgjoin("Expected match arm in form of",
              "`<pattern> => <result>`".toYellow())
    )

    if line[1] == ident("_"):
      var novars: HashSet[VarSym]
      result.add nnkElse.newTree(
        parseTermExpr(line[2], conf, novars)
      )
    else:
      let (impl, vars) = parseTermPattern(line[1], conf)
      result.add nnkElifBranch.newTree(
        newCall("unifp", ident(conf.termId), impl),
        parseTermExpr(line[2], conf, vars)
      )



macro initTRS*(fPrefix: string, term, impl: typed, body: untyped): untyped =
  # TODO infer `fPrefix` from functor symbol
  assertNodeIt(
    term,
    (term.kind == nnkSym and
     term.getTypeInst().kind == nnkBracketExpr and
     $term.getTypeInst()[0] == "Term"),
    msgjoin(
      "Expected variable of type `Term[V, F]` but found '",
      term.toStrLit().strVal().toYellow(), "' of type",
      term.getTypeInst().toStrLit().strVal().toYellow()
  ))


  assertNodeIt(
    impl,
    (impl.kind == nnkSym and
     impl.getTypeInst().kind == nnkBracketExpr and
     $impl.getTypeInst()[0] == "TermImpl"),
    msgjoin(
      "Expected variable of type `TermImpl[V, F]` but found '",
      term.toStrLit().strVal().toYellow(), "' of type",
      term.getTypeInst().toStrLit().strVal().toYellow()
  ))

  assertNodeIt(
    fPrefix,
    fPrefix.kind in {nnkStrLit, nnkIdent},
    "Expected string literal or ident for functor prefix")

  let termType = term.getTypeInst()
  result = initTRSImpl(GenParams(
    vName: termType[1].strVal(),
    fName: termType[2].strVal(),
    fPrefix: fPrefix.strVal(),
    termId: term.strVal(),
    implId: impl.strVal()
  ), body)

  # echo result.toStrLit()
