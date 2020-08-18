import macros, strformat, sets, sugar, strutils, sequtils
import trscore
import hmisc/[hexceptions, helpers]
import hmisc/types/[colorstring, initcalls]

# TODO validate functor conststruction by checking number of arguments
# (and possibly their types (it is possible /technically/))

type
  GenParams = object
    vName, fName, fPrefix, termId, implId: string
    nodecl: bool

  VarSpec = object
    isNullable: bool
    isFunc: bool
    decl: NimNode

  VarTable = Table[VarSym, VarSpec]


func mergeTable*(lhs: var VarTable, rhs: VarTable): void =
  for vsym, spec in rhs:
    if vsym notin lhs:
      lhs[vsym] = spec
    else:
      if lhs[vsym].isNullable and (not spec.isNullable):
        lhs[vsym].isNullable = false

func exceptionWrongListp(
  tbl: var VarTable, vsym, revert: VarSym, spec: VarSpec): CodeError =
    toCodeError(
      {
        spec.decl : ("Has " &
          vsym.listvarp().tern("list (@)", "scalar ($)").toGreen() &
          " prefix"),
        tbl[revert].decl : "First declared here as " &
          (not vsym.listvarp()).tern("list (@)", "scalar ($)"
          ).toGreen(),
      },
      msgjoin(
        "Variable", ($vsym).toYellow(),
        "is already declared as", ($revert).toYellow(), ".",
      )
    )


func exceptionUndefinedVar(
  tbl: VarTable, vsym: VarSym, spec: VarSpec): CodeError =
    toCodeError(
      { spec.decl : "Not declared in LHS" },
      msgjoin("Undeclared variable", ($vsym).toYellow())
    )

func usevar*(tbl: var VarTable, vsym: VarSym, spec: VarSpec): void =
  if vsym notin tbl:
    let revert = makeVarSym(vsym.getVName(), not vsym.listvarp())
    if revert in tbl:
      raise exceptionWrongListp(tbl, vsym, revert, spec)
    else:
      raise exceptionUndefinedVar(tbl, vsym, spec)

func addvar*(tbl: var VarTable, vsym: VarSym, spec: VarSpec): void =
  if vsym notin tbl:
    let revert = makeVarSym(vsym.getVName(), not vsym.listvarp())
    if revert in tbl:
      raise exceptionWrongListp(tbl, vsym, revert, spec)
    else:
      tbl[vsym] = spec
  else:
    if tbl[vsym].isNullable and (not spec.isNullable):
      tbl[vsym].isNullable = false

template mapItInfix*(topInfix: NimNode, op: untyped): untyped =
  type ResT = typeof((var it {.inject.}: NimNode; op))
  var curr = topInfix
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

  res

func parseTermPattern(
  body: NimNode, conf: GenParams, nullable: bool, vtable: var VarTable): NimNode =
  let
    fType = mkNType(conf.fName)
    vType = mkNType(conf.vName)

  case body.kind:
    of nnkCall:
      case body[0].kind:
        of nnkIdent:
          let id = body[0].strVal()
          let args = collect(newSeq):
            for arg in body[1..^1]:
              parseTermPattern(arg, conf, nullable, vtable)

          # TODO add runtime assert with `CodeError` to check if
          # implementation considers substituted term a functor. TODO
          # - disable this check in non-debug build.
          result = mkCallNode("makeFunctor", @[
            ident(conf.fPrefix & id)] &
              args.mapIt(newCall("makePattern", it)), @[vType, fType])


        of nnkBracket:
          let
            vsym = parseVarSym(body[0][0].toStrLit().strVal())
            spec = VarSpec(decl: body, isNullable: nullable, isfunc: true)
          if conf.nodecl: vtable.usevar(vsym, spec)
          else: vtable.addvar(vsym, spec)

          debugecho vsym

          result = mkCallNode(
            "makeFunctor", [vType, fType],
            @[
              makeInitAllFields(vsym),
              body[1..^1].mapIt(
                it.parseTermPattern(conf, nullable, vtable)
              ).toBracketSeq()
            ]
          )
        else:
          raiseCodeError(
            body[0],
            "Unexpected node kind",
            &"{body[0].kind}")

    of nnkIdent:
      let str = body.strVal()
      if str == "_":
        result = mkCallNode("makePlaceholder", [vType, fType])
      else:
        let vsym = parseVarSym(str)
        result = mkCallNode("makeVariable", [vType, fType],
                               makeInitAllFields(vsym))

        if conf.nodecl:
          vtable.usevar(vsym, VarSpec(decl: body, isNullable: nullable))
        else:
          vtable.addvar(vsym, VarSpec(decl: body, isNullable: nullable))
    of nnkPrefix:
      let prefstr = body[0].strval()
      case prefstr:
        of "$", "@":
          let vsym = makeVarSym(
            body[1].strVal(), islist = (body[0].strval() == "@"))
          result = mkCallNode(
            "makeVariable", [vType, fType], makeInitAllFields(vsym))

          if conf.nodecl:
            vtable.usevar(vsym, VarSpec(decl: body, isNullable: nullable))
          else:
            vtable.addvar(vsym, VarSpec(decl: body, isNullable: nullable))
        of "*", "?", "+", "!":
          let nullable = if prefstr in ["*", "?"]: true else: nullable
          case body[0].kind:
            of nnkPar:
              assertNodeIt(body[0], body[0].len == 1,
                           "Use `&` for concatenation, not commas")

              result = body[0][0].parseTermPattern(conf, nullable, vtable)
            else:
              result = body[1].parseTermPattern(conf, nullable, vtable)

          let callname =
            case prefstr:
              of "*": "makeZeroOrMoreP"
              of "+": "makeOneOrMoreP"
              of "?": "makeOptP"
              of "!": "makeNegationP"
              else: "<<<INVALID_PREFIX>>>"

          result = mkCallNode(callname, @[result])
        of "*@":
          let vsym = makeVarSym(body[1].strVal(), islist = true)

          # TODO REFACTOR
          result = mkCallNode("makeZeroOrMoreP", @[
            mkCallNode("makeVariable", [vType, fType],
                       makeInitAllFields(vsym))])

          if conf.nodecl:
            vtable.usevar(vsym, VarSpec(decl: body[1], isNullable: nullable))
          else:
            vtable.addvar(vsym, VarSpec(decl: body[1], isNullable: nullable))
        of "%", "%!":
          assertNodeIt(
            body[1],
            body[1].kind == nnkCall,
            "Expected call node",
            &"Kind is {body[1].kind}")

          if prefstr == "%":
            result = body[1]
          else:
            result = newCall("toTerm", body[1], ident conf.implId)
        of "%?":
          let predc = body[1]
          predc.assertNodeIt(
            predc.kind in {nnkCall, nnkIdent},
            "Unexpected node kind",
            &"Node kind: {body[1].kind}")

          case predc.kind:
            of nnkCall:
              result = newCall(
                "makeFunctor",
                @[
                  predc[0],
                  predc[0].toStrLit(),
                  predc[1..^1].mapIt(it.parseTermPattern(
                    conf, nullable, vtable)).toBracketSeq()
                ]
              )
            of nnkIdent:
              result = mkCallNode(
                "makeConstant", [vType, fType],
                @[ predc, predc.toStrLit() ]
              )
            else:
              raiseAssert("#[ DIE ]#")
        else:
          raiseCodeError(body[0], &"Unexpected prefix '{prefstr.toYellow()}'")
    of nnkIntLit:
      result = mkCallNode("toTerm", @[body, ident(conf.implId)])
    of nnkInfix:
      case body[0].strVal():
        of "&", "|":
          let elems: seq[NimNode] = body.mapItInfix:
            it.parseTermPattern(conf, nullable, vtable)

          let callname =
            case body[0].strVal():
              of "&": "makeAndP"
              of "|": "makeOrP"
              else: "<<<INVALID_PREFIX>>>"

          result = mkCallNode(callname, @[ elems.toBracketSeq() ])
    of nnkStmtList:
      return parseTermPattern(body[0], conf, nullable, vtable)
    else:
      raiseAssert(&"#[ IMPLEMENT for kind {body.kind} ]#")


func parseTermExpr(
  body: NimNode, conf: GenParams, vtable: VarTable): NimNode =
  var vtable = vtable
  let conf = conf.withIt:
    it.nodecl = true

  let impl = parseTermPattern(body, conf, false, vtable)
  return impl

func parseTermExpr(body: NimNode, conf: GenParams): (NimNode, VarTable) =
  var vtable: VarTable
  let impl = parseTermPattern(body, conf, false, vtable)
  return (impl, vtable)

func parseTermPattern(body: NimNode, conf: GenParams): (NimNode, VarTable) =
  var vtable: VarTable
  let impl = parseTermPattern(body, conf, false, vtable)
  return (impl, vtable)

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

func makeGenParams*(fPrefix: string, impl: NimNode): GenParams =
  impl.expectNode(nnkSym, mkNType("TermImpl", @["V", "F"]))
  # assertNodeIt(
  #   fPrefix,
  #   fPrefix.kind in {nnkStrLit, nnkIdent},
  #   "Expected string literal or ident for functor prefix")

  let implType = impl.getTypeInst()
  result = GenParams(
     vName: implType[1].strVal(),
     fName: implType[2].strVal(),
     fPrefix: fPrefix,
     implId: impl.strVal()
   )

macro initTRS*(impl: typed, body: untyped): untyped =
  result = initTRSImpl(makeGenParams(
    impl.getTypeInst()[2].getEnumPref(), impl) , body)

func discardStmtList*(body: NimNode): NimNode =
  if body.kind == nnkStmtList and body[0].kind == nnkStmtList:
    body[0]
  else:
    body

macro makeMatchTerm*[V, F](impl: TermImpl[V, F], patt: untyped): untyped =
  let conf = makeGenParams(impl.getTypeInst()[2].getEnumPref(), impl)
  let (matcher, vars) =  parseTermPattern(patt, conf)
  return matcher

macro matchWith*[V, F](
  term: Term[V, F], impl: TermImpl[V, F], patts: untyped): untyped =
  let
    conf = makeGenParams(impl.getTypeInst()[2].getEnumPref(), impl)
    termType = term.getTypeInst()
    resId = genSym(nskVar, ident = "res")
    termId = genSym(ident = "term")
    foundId = genSym(nskVar, ident = "found")

  result = newStmtList()

  result.add quote do:
    var `resId`: Option[`termType`]
    let `termId` = `term`
    var `foundId`: bool = false

  # echo patts.treeRepr()

  for idx, patt in patts.discardStmtList():
    assertNodeIt(
      patt,
      (patt.kind == nnkInfix and patt[0].strVal == "=>"),
      msgjoin("Expected match arm in form of",
              "`<pattern> => <result>`".toYellow()),
      &"Patter is {patt.kind}"
    )

    let (matcher, vars) =  parseTermPattern(patt[1], conf)
    let generator = parseTermExpr(patt[2], conf, vars)
    result.add quote do:
      if (not `foundId`) and unifp(`matcher`, `termId`):
        `resId` = some(`generator`.substitute(env))

  result.add quote do:
    `resId`

  result = newBlockStmt(result)

  # echo result.toStrLit()

macro matchPattern*[V, F](
  term: Term[V, F], impl: TermImpl[V, F], patt: untyped): untyped =
  let conf = makeGenParams(impl.getTypeInst()[2].getEnumPref(), impl)
  let (patt, vars) = patt.parseTermPattern(conf)
  let unifcall = newCall("unifp", term, patt)
  var
    vardecls: seq[NimNode]
    varassign: seq[NimNode]

  let
    vtype = ident(conf.vName)

  for varsym, spec in vars:
    let
      varid = ident(varsym.getvname)
      varn = newLit(varsym.getvname)

    vardecls.add:
      if varsym.listvarp:
        quote do:
           var `varid` {.inject.}: seq[`vtype`]
      else:
        if spec.isNullable:
          quote do:
            var `varid` {.inject.}: Option[`vtype`]
        else:
          quote do:
            var `varid` {.inject.}: `vtype`

    varassign.add:
      if varsym.listvarp:
        quote do:
          `varid` = env.getValues(makeVarSym(`varn`, true), `impl`)
      else:
        if spec.isNullable:
          quote do:
            let vars = makeVarSym(`varn`, false)
            if vars in env:
              `varid` = some(env[vars].fromTerm(`impl`))
            else:
              `varid` = none(`vtype`)
        else:
          quote do:
            `varid` = env[makeVarSym(`varn`, false)].fromTerm(`impl`)

  block:
    let vardecls = newStmtList(vardecls)
    let varassign = newStmtList(varassign)
    result = quote do:
      # echo `patt`.exprRepr(`impl`)
      `vardecls`
      if `unifcall`:
        `varassign`
        true
      else:
        false

    # echo result.toStrLit()

macro matchPattern*[V, F](
  term: V, impl: TermImpl[V, F], patt: untyped): untyped =
  quote do:
    matchPattern(toTerm(`term`, `impl`), `impl`, `patt`)
