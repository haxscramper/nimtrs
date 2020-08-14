import macros, strformat, sets
import trscore
import hmisc/[hexceptions, helpers]
import hmisc/types/colorstring


type
  GenParams = object
    vName: string
    fName: string
    fPrefix: string


func parseTermPattern(body: NimNode, conf: GenParams): (NimNode, VarSet) =
  discard

func parseTermExpr(body: NimNode, conf: GenParams, vars: VarSet): NimNode =
  discard

func makeTermMatch*(conf: GenParams, termId, body: NimNode): NimNode =
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
        newCall("unifp", termId, impl),
        parseTermExpr(line[2], conf, vars)
      )



macro termMatch*(fPrefix: string, term: typed, body: untyped): untyped =
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
    fPrefix,
    fPrefix.kind in {nnkStrLit, nnkIdent},
    "Expected string literal or ident for functor prefix")

  let termType = term.getTypeInst()
  result = makeTermMatch(GenParams(
    vName: termType[1].strVal(),
    fName: termType[2].strVal(),
    fPrefix: fPrefix.strVal()
  ), term, body)

  echo result.toStrLit()
