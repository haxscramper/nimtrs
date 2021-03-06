## Term algorithms. Implmenetation uses callback functions for getting
## values/types from terms.

import std/[
  options, deques, intsets, sets, hashes, sequtils,
  tables, strformat, strutils, sugar, macros
]

export tables, intsets

import
  hmisc/extra/hdrawing/[term_buf],
  hmisc/types/[seq2d, colorstring, htrie, hprimitives],
  hmisc/macros/[iflet, cl_logic],
  hmisc/algo/[halgorithm, hseq_mapping, htree_mapping],
  hmisc/[helpers, hexceptions]

export colorstring
# type
#   InfoException = ref object of CatchableError

#   GenException*[T] = ref object of InfoException
#     info*: T


# proc raiseGenEx[T](msg: string, info: T): void =
#   var tmp = new GenException[T]
#   tmp.msg = msg & " [generic exception, T is `" & $typeof(T) & "`]"
#   tmp.info = info
#   raise tmp

# template getGEx*[T](): untyped = cast[GenException[T]](getCurrentException())


type

  TermPatternKind* = enum
    tpkZeroOrMore
    tpkAlternative
    tpkNegation
    tpkConcat
    tpkOptional
    tpkTerm

  TermPattern*[V, F] = object
    case kind*: TermPatternKind
      of tpkZeroOrMore, tpkOptional, tpkNegation:
        patt*: SingleIt[TermPattern[V, F]]
      of tpkConcat, tpkAlternative:
        patterns*: seq[TermPattern[V, F]]
      of tpkTerm:
        term*: SingleIt[Term[V, F]]


  TermKind* = enum
    tkVariable
    tkFunctor
    tkConstant
    tkPlaceholder
    tkList
    tkPattern

  VarSym* = object
    isList: bool
    name: string

  VarSet* = HashSet[VarSym]

  SubstitutionErrorInfo* = object
    path*: TreePath
    case kind*: TermKind:
      of tkVariable:
        vname*: VarSym
      else:
        discard


  FuncHeadKind* = enum
    fhkValue
    fhkPredicate
    fhkVariable

  Term*[V, F] = object
    case tkind*: TermKind
      of tkFunctor:
        case headKind*: FuncHeadKind:
          of fhkValue: ## functor symbols - constant
            functor: F
          of fhkPredicate: ## Functor head predicate
            funcPred: proc(fhead: F): bool {.noSideEffect.}
            funcPredRepr*: string
            case bindHead: bool
              of true:
                headVar: VarSym ## Functor head variable
              of false:
                discard
          of fhkVariable:
            funcVariable: VarSym ## Functor head variable

        arguments: SingleIt[Term[V, F]]
      of tkConstant:
        case bindConst: bool
          of true:
            constVar: VarSym
          of false:
            discard

        case isPredicate: bool
          of true:
            constPred: proc(val: V): bool {.noSideEffect.}
            constPredRepr*: string
          of false:
            case isFunctor: bool
              of false:
                csym: F
                value: V
              of true:
                fsym: F

      of tkVariable:
        name: VarSym
      of tkList:
        elements: seq[Term[V, F]]
      of tkPattern:
        fullMatch: bool
        pattern: TermPattern[V, F]
      of tkPlaceholder:
        nil


  TermImpl*[V, F] = object
    ## Callback procs for concrete types.
    ##
    ## 'Implementation' of certain actions for concrete types `V` and `F`.
    ##
    ## ## Example
    ##
    ## Example for `NimNode` and `NimNodeKind`
    ##
    ## .. code-block:: nim
    ##
    ##     func isFunctor*(nnk: NimNodeKind): bool =
    ##       nnk notin {
    ##         nnkNone, nnkEmpty, nnkNilLit, # Empty node
    ##         nnkCharLit..nnkUInt64Lit, # Int literal
    ##         nnkFloatLit..nnkFloat64Lit, # Float literal
    ##         nnkStrLit..nnkTripleStrLit, nnkCommentStmt, nnkIdent, nnkSym # Str lit
    ##       }
    ##
    ##     const nimAstImpl* = TermImpl[NimNode, NimNodeKind](
    ##       getsym: (proc(n: NimNode): NimNodeKind = n.kind),
    ##       isFunctorSym: (proc(kind: NimNodeKind): bool = kind.isFunctor()),
    ##       makeFunctor: (
    ##         proc(op: NimNodeKind, sub: seq[NimNode]): NimNode =
    ##           if sub.len == 0: newNimNode(op)
    ##           else: newTree(op, sub)
    ##       ),
    ##       getArguments: (proc(n: NimNode): seq[NimNode] = toSeq(n.children)),
    ##       valStrGen: (proc(n: NimNode): string = $n.toStrLit()),
    ##     )

    isFunctorSym*: proc(val: F): bool {.noSideEffect.}
    getArguments*: proc(val: V): seq[V] {.noSideEffect.}
    getSym*: proc(val: V): F {.noSideEffect.}
    makeFunctor*: proc(sym: F, subt: seq[V]): V {.noSideEffect.}
    makeList*: proc(subt: seq[V]): V {.noSideEffect.}
    valStrGen*: proc(val: V): string {.noSideEffect.}## Conver value
    ## to string.

  TermEnv*[V, F] = object
    ## Mapping between variable symbols and values
    values*: Table[VarSym, Term[V, F]]

  GenProc*[V, F] = proc(env: TermEnv[V, F]): Term[V, F] ## Proc for
  ## generaing Values during rewriting.
  DefaultGenProc*[V, F] = proc(
    env: TermEnv[V, F]): TermEnv[V, F] {.noSideEffect.} ## Generate
  ## default values for variables

  MatchProc*[V, F] = proc(test: Term[V, F]): Option[TermEnv[V, F]]

  TermGenerator*[V, F] = object
    case isPattern*: bool
      of true:
        patt*: Term[V, F]
      of false:
        gen*: GenProc[V, F]

  MatcherList*[V, F] = object
    first: Table[F, seq[int8]]
    forceTry: seq[int8] ## List of matchers to always try
    patterns*: seq[TermMatcher[V, F]]
    # default: DefaultGenProc[V, F]

  PattList*[V, F] = Table[VarSym, MatcherList[V, F]]

  TermMatcher*[V, F] = object
    case isPattern*: bool
      of true:
        patt*: Term[V, F]
      of false:
        matcher*: MatchProc[V, F]

    subpatts*: Table[VarSym, MatcherList[V, F]] ## Submatches
    ## on generated variables
    varlist: VarSet ## List of generated variables
    # `varlist` can be automatically genrated for pattern-based term
    # matchers. If matcher proc is used user should supply list of
    # variable names.
    default: DefaultGenProc[V, F] ## Generate missing variables not produced
    ## by subpattern matches
    optVars: VarSet ## Optional variables - `default` is not required
                    ## to generate them.


  RulePair*[V, F] = object
    matchers*: MatcherList[V, F]
    # rules*: seq[TermMatcher[V, F]] # List of patterns/matchers
    # first: Table[F, seq[int8]] # Functor -> Possible pattern
    # matchers: seq[int8] # List of matchers
    gen*: TermGenerator[V, F] # Proc to generate final result

  RuleId* = int16
  RedSystem*[V, F] = object
    first: Table[F, seq[RuleId]]
    matchers: set[RuleId] # Matcher procs - always have to try
    rules: seq[RulePair[V, F]]

#=====================  reduction constraint types  ======================#

type
  ReduceConstraints* = enum
    rcNoConstraints
    rcRewriteOnce
    rcApplyOnce

  ReductionState = object
    rewPaths: Trie[int, set[RuleId]]
    constr: ReduceConstraints
    maxDepth: int


proc registerUse(rs: var ReductionState, path: TreePath, id: RuleId): void =
  case rs.constr:
    of rcApplyOnce:
      if path notin rs.rewPaths:
        var tmp: set[RuleId]
        rs.rewPaths[path] = tmp

      rs.rewPaths[path].incl id
    of rcRewriteOnce:
      var tmp: set[RuleId]
      rs.rewPaths[path] = tmp

    else:
      discard

proc canRewrite(rs: ReductionState, path: TreePath): bool =
  path.len < rs.maxDepth and not (
    # Avoid rewriting anyting on this path
    rs.constr == rcRewriteOnce and
    rs.rewPaths.prefixHasValue(path)
  )


proc cannotUse(rs: ReductionState, path: TreePath, rule: RuleId): bool =
    # Avoid using this rule again on the same path
    (rs.constr == rcApplyOnce) and
    (rs.rewPaths.prefixHasValue(path)) and
    toSeq(rs.rewPaths.prefixedValues(path)).anyOfIt(rule in it)

#==========================  making new terms  ===========================#

func makePattern*[V, F](patt: TermPattern[V, F],
                        fullMatch: bool = false): Term[V, F] =
  Term[V, F](pattern: patt,
             tkind: tkPattern,
             fullmatch: fullmatch)

func makePattern*[V, F](patt: Term[V, F]): Term[V, F] =
  patt

func makeVarSym*(name: string, islist: bool): VarSym =
  VarSym(name: name, islist: islist)

func initVarSym*(name: string, islist: bool): VarSym =
  VarSym(name: name, islist: islist)

func parseVarSym*(str: string): VarSym =
  if str[0] == '@': makeVarSym(str[1..^1], true)
  elif str[0] == '$': makeVarSym(str[1..^1], false)
  else: makeVarSym(str, false)

func parseVarSym*(node: NimNode): VarSym =
  assert node.kind == nnkPrefix and node[1].kind == nnkIdent
  if node[0] == ident("@"):
    makeVarSym(node[1].strval(), true)
  elif node[0] == ident("$"):
    makeVarSym(node[1].strval(), false)
  else:
    raiseAssert("Invalid prefix for varsym")

func makePlaceholder*[V, F](): Term[V, F] =
  Term[V, F](tkind: tkPlaceholder)

func makeConstant*[V, F](val: V, csym: F): Term[V, F] =
  Term[V, F](
    isPredicate: false,
    isFunctor: false,
    tkind: tkConstant,
    value: val,
    csym: csym
  )

func makeConstant*[V, F](
  constPred: proc(val: V): bool {.noSideEffect.},
  constPredRepr: string): Term[V, F] =
  Term[V, F](
    isPredicate: true,
    tkind: tkConstant,
    constPred: constPred,
    constPredRepr: constPredRepr,
    bindConst: false)

func makeConstant*[V, F](fsym: F): Term[V, F] =
  Term[V, F](
    isPredicate: false,
    isFunctor: true,
    tkind: tkConstant,
    fsym: fsym
  )

func makeConstant*[V, F](val: V, csym: F, constVar: VarSym): Term[V, F] =
  Term[V, F](
    isPredicate: false,
    tkind: tkConstant,
    isFunctor: false,
    bindConst: true,
    csym: csym,
    value: val,
    # bindVar: true,
    constVar: constVar)

func makeVariable*[V, F](name: string, isList: bool = false): Term[V, F] =
  Term[V, F](tkind: tkVariable, name: makeVarSym(name, isList))


# func makeVariableFunctor*[V, F](vsym: VarSym, islist: bool = false)

func makeVariable*[V, F](vsym: VarSym): Term[V, F] =
  Term[V, F](tkind: tkVariable, name: vsym)

# func makeVariable*[V, F](idx: int): Term[V, F] =
#   Term[V, F](tkind: tkVariable, name: makeVarSym(idx))

func makeList*[V, F](elements: seq[Term[V, F]]): Term[V, F] =
  Term[V, F](tkind: tkList, elements: elements)

func makeFunctor*[V, F](
  sym: F, subt: seq[Term[V, F]]): Term[V, F] =
  Term[V, F](
    headKind: fhkValue,
    tkind: tkFunctor,
    functor: sym,
    arguments: makeList(subt).newIt())

func makeFunctor*[V, F](
  headvar: VarSym, subt: seq[Term[V, F]]): Term[V, F] =
  Term[V, F](
    headKind: fhkVariable,
    tkind: tkFunctor,
    funcVariable: headvar,
    arguments: makeList(subt).newIt())

func makeFunctor*[V, F](
  funcPred: proc(fhead: F): bool {.noSideEffect.},
  funcPredRepr: string,
  subt: seq[Term[V, F]]): Term[V, F] =
  Term[V, F](
    funcPred: funcPred,
    funcPredRepr: funcPredRepr,
    headKind: fhkPredicate,
    tkind: tkFunctor,
    bindHead: false,
    arguments: makeList(subt).newIt())

func makeFunctor*[V, F](
  funcPred: proc(fhead: F): bool {.noSideEffect.},
  funcPredRepr: string,
  headVar: VarSym, subt: seq[Term[V, F]]): Term[V, F] =
  ## Create predicate functor with head binding to variable
  ## `predVar`
  # TODO:DOC what is `funcPredVar`
  Term[V, F](
    funcPred: funcPred,
    headKind: fhkPredicate,
    funcPredRepr: funcPredRepr,
    tkind: tkFunctor,
    bindHead: true,
    headVar: headVar,
    arguments: makeList(subt).newIt())

func makeFunctor*[V, F](sym: F, subt: varargs[Term[V, F]]): Term[V, F] =
  ## Create functor using `sym` as functor head and `subt` as arguments.
  makeFunctor(sym, toSeq(subt))




#===========================  Making patterns  ===========================#

func makeTermP*[V, F](patt: Term[V, F]): TermPattern[V, F] =
  ## Convert term to pattern matching this term
  TermPattern[V, F](kind: tpkTerm, term: newIt(patt))

func makeAndP*[V, F](patts: seq[TermPattern[V, F]]): TermPattern[V, F] =
  ## Create 'and' pattern from sequence of patterns: `E1 & E2 &E3 ...`
  TermPattern[V, F](kind: tpkConcat, patterns: patts)

# func makeAndP*[V, F](
#   patts: varargs[TermPattern[V, F]]): TermPattern[V, F] =
#   TermPattern[V, F](kind: tpkConcat, patterns: toSeq(patts))

func makeAndP*[V, F](
  patts: varargs[TermPattern[V, F], makeTermP]): TermPattern[V, F] =
  ## Create 'and' pattern from all arguments: `E1 & E2 & E3`
  TermPattern[V, F](kind: tpkConcat, patterns: toSeq(patts))

func makeOrP*[V, F](patts: seq[TermPattern[V, F]]): TermPattern[V, F] =
  ## Create 'or' pattern from all arguments: `E1 | E2 | E2`
  TermPattern[V, F](kind: tpkAlternative, patterns: patts)

func makeOptP*[V, F](patt: TermPattern[V, F]): TermPattern[V, F] =
  ## Create optional pattern from argument: `?E`
  TermPattern[V, F](kind: tpkOptional, patt: newIt(patt))

func makeOptP*[V, F](patt: Term[V, F]): TermPattern[V, F] =
  ## Create optional pattern from term argument: `?T`
  TermPattern[V, F](kind: tpkOptional, patt: newIt(patt.makeTermP()))

func makeZeroOrMoreP*[V, F](patt: TermPattern[V, F]): TermPattern[V, F] =
  ## Create zero-or-more pattern from argument: `*E`
  TermPattern[V, F](kind: tpkZeroOrMore, patt: newIt(patt))

func makeZeroOrMoreP*[V, F](patt: Term[V, F]): TermPattern[V, F] =
  ## Create zero-or-more patern from term argument: `*T`
  TermPattern[V, F](kind: tpkZeroOrMore, patt: newIt(patt.makeTermP()))

func makeNegationP*[V, F](patt: TermPattern[V, F]): TermPattern[V, F] =
  ## Create negation patter from term: `!E`
  TermPattern[V, F](kind: tpkNegation, patt: newIt(patt))


func makeTermPattern*[V, F](patt: TermPattern[V, F]): TermPattern[V, F] =
  ## Convert term pattern to term pattern (used to simplify DSL)
  patt

func makeTermPattern*[V, F](patt: Term[V, F]): TermPattern[V, F] =
  ## Convert term term to term pattern. Used in DSL - in regular code
  ## you might want to use `makeTermP`
  patt.makeTermP()

#============================  Aux functions  ============================#

func hash*(vs: VarSym): Hash =
  var h: Hash = 0
  h = h !& hash(vs.isList) !& hash(vs.name)
  result = !$h

func `==`*(l, r: VarSym): bool = l.isList == r.isList and l.name == r.name

func `==`*(l: VarSym, str: string): bool =
  case str[0]:
    of '@': (l.isList and l.name == str[1..^1])
    of '_': (not l.isList and l.name == str[1..^1])
    else: (not l.isList and l.name == str)

#======================  accessing term internals  =======================#

func listvarp*(vs: VarSym): bool = vs.isList
func getVName*(vs: VarSym): string = vs.name
func varp*[V, F](t: Term[V, F]): bool = (t.tkind == tkVariable)
func predp*[V, F](t: Term[V, F]): bool =
  (t.tkind == tkFunctor and t.headKind == fhkPredicate) or
  (t.tkind == tkConstant and t.isPredicate)

func functorvalp*[V, F](t: Term[V, F]): bool =
  t.tkind == tkConstant and (not t.isPredicate) and t.isFunctor

func listvarp*[V, F](t: Term[V, F]): bool =
  t.tkind == tkVariable and t.name.listvarp()

func bindvarp*[V, F](t: Term[V, F]): bool =
  (t.tkind == tkFunctor and t.headKind == fhkPredicate and t.bindHead) or
  (t.tkind == tkConstant and t.isPredicate and t.bindConst)


func exprRepr*(vs: VarSym): string =
  if vs.listvarp:
    "@" & vs.name
  else:
    "$" & vs.name

func `$`*(vs: VarSym): string = vs.exprRepr()

func getKind*[V, F](t: Term[V, F]): TermKind =
  t.tkind

func getVName*[V, F](t: Term[V, F]): VarSym =
  if t.tkind == tkVariable:
    t.name
  elif t.tkind == tkFunctor and t.headKind == fhkVariable:
    t.funcVariable
  elif t.bindvarp():
    t.headVar
  else:
    raiseAssert("Invalid term to get variable name from")


func getFSym*[V, F](t: Term[V, F]): F =
  assert (t.getKind() == tkFunctor and t.headKind == fhkValue) or
    (t.getKind() == tkConstant and t.isFunctor)
  if t.tkind == tkFunctor:
    t.functor
  else:
    t.fsym

func getSym*[V, F](t: Term[V, F]): F =
  ## Get functor symbols from term
  case t.getKind():
    of tkFunctor: t.functor
    of tkConstant: t.csym
    else:
      raiseAssert(
        "Invalid term kind - cannot get symbol from " & $t.getKind())

func getNth*[V, F](
  t: Term[V, F], idx: int): Term[V, F]=
  ## Get nth argument from functor or nth element from list
  let k = t.getKind()
  assert k in {tkFunctor, tkList}
  if k == tkList:
    return t.elements[idx]
  else:
    return t.arguments.getIt().elements[idx]

func getPatt*[V, F](t: Term[V, F]): TermPattern[V, F] =
  assert t.tkind == tkPattern
  t.pattern

func getNthMod*[V, F](
  t: var Term[V, F], idx: int): var Term[V, F] =
  ## Get mutable value of [`idx`] element in list or functor arguments
  let k = t.getKind()
  assert k in {tkFunctor, tkList}
  if k == tkList:
    return t.elements[idx]
  else:
    return t.arguments.getIt().elements[idx]

func getArguments*[V, F](t: Term[V, F]): seq[Term[V, F]] =
  ## Get sequence of functor arguments
  assert t.getKind() == tkFunctor
  t.arguments.getIt().elements

func getArgumentList*[V, F](t: Term[V, F]): Term[V, F] =
  ## Get functor arguments as a single list term.
  assert t.getKind() == tkFunctor
  t.arguments.getIt()

func getElements*[V, F](t: Term[V, F]): seq[Term[V, F]] =
  ## Get elements from list term
  assert t.getKind() == tkList
  t.elements

func addElement*[V, F](t: var Term[V, F], elem: Term[V, F]): void =
  ## Append element to list term
  assert t.getkind == tkList
  t.elements.add elem

func setSubt*[V, F](t: var Term[V, F], subt: seq[Term[V, F]]): void =
  ## Set arguments for functor
  assert t.getKind() == tkFunctor
  t.subterms = subt

func getValue*[V, F](self: Term[V, F]): V =
  ## Get value of constant term
  assert self.getKind() == tkConstant
  self.value

#======================  checking possible matches  ======================#

func hasForceTry[V, F](rule: RulePair[V, F]): bool =
  ## Return true if any rule in matcher is mandatory to try (proc
  ## matcher)
  rule.matchers.forceTry.len > 0

#===========================  pretty-printing  ===========================#
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
  let color = not defined(plainStdout)
  case term.getKind():
    of tkPattern:
      term.getPatt().exprRepr(cb)
    of tkList:
      "[" & getElements(term).mapIt(exprRepr(it, cb)).join(", ") & "]"
    of tkConstant:
      if term.predp():
        "%?".toMagenta(color) & term.constPredRepr
      else:
        if term.functorvalp():
          $term.getFSym()
        else:
          "'" & cb.valStrGen(term.getValue()) & "'"
    of tkVariable:
      term.getVName().exprRepr()
    of tkFunctor:
      let args =
        term.getArguments().mapIt(it.exprRepr(cb)).join(", ").wrap("()")
      # debugecho term.headKind
      case term.headKind:
        of fhkValue:
          if ($getSym(term)).validIdentifier():
            $getSym(term) & "(" & term.getArguments().mapIt(
              it.exprRepr(cb)).join(", ") & ")"
          else:
            let subt = term.getArguments()
            case subt.len():
              of 1: &"{term.getSym()}({subt[0].exprRepr(cb)})"
              of 2: &"{subt[0].exprRepr(cb)} {term.getSym()} {subt[1].exprRepr(cb)}"
              else: args

        of fhkPredicate:
          "%?".toMagenta(color) & term.funcPredRepr &
            term.bindvarp().tern(&"[{term.getVname().exprRepr()}]", "") &
            args
        of fhkVariable:
          &"[{term.getVName().exprRepr().toYellow(color)}]({args})"

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




#=======================  converting to/from term  =======================#

proc isFunctor*[V, F](cb: TermImpl[V, F], val: V): bool =
 ## Check if symbol for value `V` is a functor
 cb.isFunctorSym(cb.getSym(val))

proc toTerm*[V, F](val: V, cb: TermImpl[V, F]): Term[V, F] =
  ## Recursively convert value `V` to term using implementation `cb`
  if cb.isFunctor(val):
    return makeFunctor[V, F](
      cb.getSym(val), cb.getArguments(val).mapIt(it.toTerm(cb)))
  else:
    return makeConstant[V, F](val, cb.getSym(val))

proc fromTerm*[V, F](
  term: Term[V, F], cb: TermImpl[V, F], path: TreePath = @[0]): V =
  ## Convert `term` back to value type `V` using implementation `cb`.
  ## `term` MUST be fully substituted - e.g. no placeholder or
  ## variable terms must be present in tree.
  if term.getKind() notin {tkFunctor, tkConstant, tkList}:
    raiseAssert(
      "Cannot convert under-substituted term back to tree. " &
      $term.getKind() & " has to be replaced with value" &
      "Term: " & term.exprRepr(cb)
    )

  if term.getKind() == tkFunctor:
    mixin exprRepr
    template compilesOrElse(body, elseval: untyped): untyped =
      when compiles(body):
        body
      else:
        elseval

    if term.headKind != fhkValue:
      raiseAssert(msgjoin(
        "Cannot convert under-substituted term back to tree.",
        "Functor head ", compilesOrElse(term.exprRepr(cb).wrap("``"), ""),
        " has to be replaced with value"
      ))

    let fs = term.getFSym()
    if not cb.isFunctorSym(fs):
      raiseAssert(
        &"Term uses {fs} as functor head," &
          "but this is not a functor symbol according to implementation")

    # var arguments: seq[V]
    # for idx, arg in term.getArguments():
    #   if arg.listvarp():
    #     for val in
    result = cb.makeFunctor(
      term.getFSym(),
      term.getArguments().mapPairs(rhs.fromTerm(cb, path & @[lhs])))
  elif term.getKind() == tkList:
    let elems: seq[V] = term.getElements().mapPairs(
      rhs.fromTerm(cb, path & @[lhs]))
    result = cb.makeList(elems)
  else:
    result = term.getValue()






#==================================  2  ==================================#
proc assertCorrect*[V, F](impl: TermImpl[V, F]): void =
  ## Check if all fields in `impl` have been correctly initalized
  for name, value in impl.fieldPairs():
    assert (not value.isNil()), name & " cannot be nil"

func makeMatcherList*[V, F](
  matchers: seq[TermMatcher[V, F]]): MatcherList[V, F] =
  result.patterns = matchers

  for id, rule in matchers:
    case rule.isPattern:
      of true:
        result.first.mgetOrPut(rule.patt.getSym(), @[]).add id.int8
      of false: result.forceTry.add id.int8


func makeRulePair*[V, F](
  rules: seq[TermMatcher[V, F]],
  gen: TermGenerator[V, F]): RulePair[V, F] =
  result.gen = gen
  result.matchers = makeMatcherList(rules)


func varlist*[V, F](term: Term[V, F],
                    path: TreePath = @[0]): seq[(Term[V, F], TreePath)] =
  ## Output list of all variables in term
  case getKind(term):
    of tkConstant, tkPlaceholder:
      return @[]
    of tkVariable:
      return @[(term, path)]
    of tkFunctor:
      for idx, sub in getArguments(term):
        result &= sub.varlist(path & @[idx])
    of tkList:
      for idx, sub in getElements(term):
        result &= sub.varlist(path & @[idx])

    of tkPattern:
      raiseAssert("#[ IMPLEMENT ]#")


func makeMatcher*[V, F](matcher: MatchProc[V, F]): TermMatcher[V, F] =
  ## Create term matcher instance for matching procs
  TermMatcher[V, F](isPattern: false, matcher: matcher)

func makeMatcher*[V, F](patt: Term[V, F]): TermMatcher[V, F] =
  TermMatcher[V, F](isPattern: true, patt: patt)

func mergeVarlists[V, F](matchers: PattList[V, F]): VarSet =
  ## Combine sets of exported variables from multiple matchers
  if matchers.len > 0:
    return matchers.mapPairs(
      rhs.patterns.mapIt(it.varlist).foldl(union(a, b))
    ).foldl(union(a, b))

func getExportedVars[V, F](patt: TermMatcher[V, F]): VarSet =
  if patt.isPattern:
    for (v, path) in patt.patt.varlist():
      result.incl v.name

func getExportedVars*[V, F](patts: PattList[V, F]): VarSet =
  ## Get list of variables that might be generated by patters in `patts`
  result = mergeVarlists(patts)
  for vars, matcherList in patts:
    for patt in matcherList.patterns:
      result.incl patt.getExportedVars()

func exportedVars*[V, F](matcher: TermMatcher[V, F]): VarSet = matcher.varlist


func toPattList*[V, F](patts: varargs[(VarSym, Term[V, F])]): PattList[V, F] =
  toTable(patts.mapPairs((lhs, makeMatcherList(@[ rhs.makeMatcher() ]))))

func toPattList*[V, F](patts: varargs[(string, Term[V, F])]): PattList[V, F] =
  patts.mapPairs((lhs.parseVarSym(), rhs)).toPattList()
  # toTable(patts.mapPairs((lhs, makeMatcherList(@[ rhs.makeMatcher() ]))))



func makeRulePair*[V, F](
  rule: TermMatcher[V, F], gen: TermGenerator[V, F]): RulePair[V, F] =
  ## Create rule pair insance
  makeRulePair(@[rule], gen)

func setSubpatterns*[V, F](
  matcher: var TermMatcher[V, F],
  subpatts: PattList[V, F],
  default: DefaultGenProc[V, F],
  optVars: seq[VarSym]): void =
  matcher.default = default
  matcher.subpatts = subpatts
  matcher.varlist.incl getExportedVars(matcher)
  matcher.varlist.incl getExportedVars(subpatts)
  matcher.optVars = optVars.toHashSet()

func makeMatcher*[V, F](
  matcher: MatchProc[V, F],
  subpatt: PattList[V, F],
  default: GenProc[V, F],
  optVars: seq[VarSym] = @[]): TermMatcher[V, F] =
  ## Create term matcher instance for matching procs
  result = TermMatcher[V, F](isPattern: false, matcher: matcher)
  result.setSubpatterns(subpatt, default, optVars)

func makeMatcher*[V, F](
  patt: Term[V, F],
  subpatt: PattList[V, F],
  default: DefaultGenProc[V, F],
  optVars: seq[VarSym] = @[]): TermMatcher[V, F] =
  result = TermMatcher[V, F](isPattern: true, patt: patt)
  result.setSubpatterns(subpatt, default, optVars)


func makeMatcher*[V, F](
  matchers: seq[TermMatcher[V, F]],
  default: DefaultGenProc[V, F],
  optVars: seq[VarSym] = @[]): TermMatcher[V, F] =
  ## Create new toplevel term matcher from multiple smaller ones. New
  ## variable `auxToplevelCatchall` is introduced.
  let catchallName: VarSym = makeVarSym("auxToplevelCatchall", false)
  makeMatcher(
    makeVariable[V, F](catchallName),
    {
      catchallName : makeMatcherList(matchers)
    }.toTable(),
    default,
    optVars
  )


func makeGenerator*[V, F](obj: Term[V, F]): TermGenerator[V, F] =
  ## Create closure proc that will output `obj` as value
  TermGenerator[V, F](isPattern: true, patt: obj)

func makeGenerator*[V, F](obj: GenProc[V, F]): TermGenerator[V, F] =
  ## Create closure proc that will output `obj` as value
  TermGenerator[V, F](isPattern: false, gen: obj)

func makeEnvironment*[V, F](values: seq[(VarSym, Term[V, F])] = @[]): TermEnv[V, F] =
  ## Create new environment using `values` as initial binding values
  TermEnv[V, F](values: values.toTable())

func makeReductionSystem*[V, F](
  rules: seq[RulePair[V, F]]): RedSystem[V, F] =
  result.rules = rules
  for id, rule in rules:
    for fsym, _ in rule.matchers.first:
      # Try pattern only if first functor matches
      result.first.mgetOrPut(fsym, @[]).add RuleId(id)

    if rule.hasForceTry():
      # Always call matcher procs
      result.matchers.incl RuleId(id)

  for fsym, rules in result.first:
    result.first[fsym] = rules.deduplicate()

func makeReductionSystem*[V, F](
  args: varargs[RulePair[V, F]]): RedSystem[V, F] =
  makeReductionSystem(toSeq(args))


func isBound*[V, F](env: TermEnv[V, F], term: VarSym): bool =
  ## Check if variable is bound to somethin in `env`
  (term in env.values) # and env[term] != term

template getValImpl(): untyped {.dirty.} =
  ## Access value from environment.
  try:
    return e.values[t]
  except KeyError:
    # TODO check if `VarSym` can be converter to string
    # TODO use define to constrol exception verbosity
    let vars = e.mapPairs(lhs.exprRepr()).joinq()
    raise newException(
      KeyError,
      &"Missing variable `{t}` in environment. Have vars: {vars}")



func getVal*[V, F](e: TermEnv[V, F], t: VarSym): Term[V, F] =
  getValImpl()

func getVal*[V, F](e: var TermEnv[V, F], t: VarSym): var Term[V, F] =
  getValImpl()

type TermVar[V, F] = VarSym | Term[V, F] | string

func `[]`*[V, F](env: TermEnv[V, F], term: TermVar[V, F]): Term[V, F] =
  env.getVal:
    typeCondIt term:
      [string, parsevarsym(it)]
      [Term[V, F], it.name]

func `[]`*[V, F](env: var TermEnv[V, F], term: TermVar[V, F]): var Term[V, F] =
  env.getVal:
    typeCondIt term:
      [string, parsevarsym(it)]
      [Term[V, F], it.name]


func `[]=`*[V, F](env: var TermEnv[V, F],
                  lhs: TermVar[V, F], rhs: Term[V, F]): void =
  ## Add rule to environment
  let key: VarSym = typeCondIt lhs:
    [string, parseVarSym(it)]
    [Term[V, F], it.name]

  env.values[key] = rhs

func `[]=`*[V, F](system: var RedSystem[V, F],
                  lhs: TermVar[V, F], rhs: Term[V, F]): void =
  ## Add rule to environment
  let key: VarSym = typeCondIt lhs:
    [string, parseVarSym(it)]
    [Term[V, F], it.name]

  system.rules[key] = rhs

func `==`*[V, F](lhs, rhs: Term[V, F]): bool =
  lhs.tkind == rhs.tkind and (
    case lhs.tkind:
      of tkConstant: lhs.value == rhs.value
      of tkVariable: lhs.name == rhs.name
      of tkFunctor:
        lhs.functor == rhs.functor and
        lhs.arguments.getIt() == rhs.arguments.getIt()
      of tkPlaceholder: true
      of tkList:
         subnodesEq(lhs, rhs, elements)
      of tkPattern:
        raiseAssert(msgjoin("Cannot compare patterns for equality"))
  )

iterator items*[V, F](system: RedSystem[V, F]): RulePair[V, F] =
  ## Iterate over all rules in rewriting system
  for pair in system.rules:
    yield pair

iterator pairs*[V, F](system: RedSystem[V, F]): (RuleId, RulePair[V, F]) =
  ## Iterate over all rules with their indices in rewriting system
  for idx, pair in system.rules:
    yield (RuleId(idx), pair)


iterator pairs*[V, F](env: TermEnv[V, F]): (VarSym, Term[V, F]) =
  ## Iterate over all variables and values in evnironment
  for lhs, rhs in pairs(env.values):
    yield (lhs, rhs)

func getValues*[V, F](
  env: TermEnv[V, F], vsym: VarSym,
  impl: TermImpl[V, F]): seq[V] =
  env[vsym].getElements().mapIt(fromTerm(it, impl))

func contains*(vset: VarSet, vname: string): bool =
  vname.parseVarSym() in vset

func contains*[V, F](env: TermEnv[V, F], vsym: VarSym): bool =
  vsym in env.values

func contains*[V, F](env: TermEnv[V, F], term: Term[V, F]): bool =
  term.getVName() in env.values

func contains*[V, F](env: TermEnv[V, F], vname: string): bool =
  vname.parseVarSym() in env.values

func hasAll*[V, F](env: TermEnv[V, F], varlist: VarSet): bool =
  result = true
  for vname in varlist:
    if vname notin env:
      return false

func missingVars*[V, F](env: TermEnv[V, F], varlist: VarSet): VarSet =
  for vname in varlist:
    if vname notin env:
      result.incl vname

func varlist*[V, F](env: TermEnv[V, F]): VarSet =
  for vname, _ in env:
    result.incl vname

func len*[V, F](env: TermEnv[V, F]): int =
  ## Get number of itesm in enviroenmt
  env.values.len()

func bindTerm[V, F](
  variable, value: Term[V, F], env: TermEnv[V, F], ): TermEnv[V, F]

func copy*[V, F](term: Term[V, F], env: TermEnv[V, F]): (Term[V, F], TermEnv[V, F]) =
  ## Create copy of a term. All variables are replaced with new ones.
  # DOC what is returned?
  let inputEnv = env
  case getKind(term):
    of tkConstant:
      return (term, inputEnv)
    of tkVariable:
      let deref = term.dereference(env)
      if getKind(deref) == tkVariable:
        var newVar = term
        # inc newVar.genIdx
        var resEnv = bindTerm(deref, newVar, env)
        return (newVar, resEnv)
      else:
        return (deref, inputEnv)

    of tkFunctor, tkList:
      let islist = (getKind(term) == tkList)

      var
        resEnv = env
        subterms: seq[Term[V, F]]

      for arg in islist.tern(getArguments(term), getElements(term)):
        let (tmpArg, tmpEnv) = arg.copy(resEnv)
        resEnv = tmpEnv
        subterms.add tmpArg

      if islist:
        return (makeList(subterms), resEnv)
      else:
        return (makeFunctor(getFSym(term), subterms), resEnv)

    of tkPlaceholder:
      return (term, inputEnv)
    of tkPattern:
      raiseAssert("#[ IMPLEMENT ]#")


func bindTerm[V, F](variable, value: Term[V, F], env: TermEnv[V, F]): TermEnv[V, F] =
  ## Create environment where `variable` is bound to `value`
  result = env
  case getKind(value):
    of tkConstant, tkVariable, tkPlaceholder, tkList, tkPattern:
      result.appendOrUnif(variable, value)
      result[getVName(variable)] = value
    of tkFunctor:
      let (newTerm, newEnv) = value.copy(env)
      result = newEnv
      result[getVName(variable)] = newTerm

func dereference*[V, F](
  term: Term[V, F], env: TermEnv[V, F], ): Term[V, F]=
  ## Traverse binding chain in environment `env` and return value of
  ## the `term`
  result = term

  while getKind(result) == tkVariable and isBound(env, getVName(result)):
    let value = env[getVName(result)]
    if getKind(value) == tkConstant or value == result:
      result = value
      break

    result = value

func derefOrDefault*[V, F](
  term: Term[V, F], env: TermEnv[V, F], default: Term[V, F]): Term[V, F] =
  if term in env:
    return dereference(term,  env)
  else:
    default


func unif*[V, F](
  t1, t2: Term[V, F], env: TermEnv[V, F], level: int): Option[TermEnv[V, F]]

func partialMatch[V, F](
  elems: seq[Term[V, F]],
  startpos: int,
  patt: TermPattern[V, F],
  env: TermEnv[V, F],
  level: int): tuple[env: Option[TermEnv[V, F]], shift: int] =
  ## Apply pattern `patt` to subsequence `elems[startpos .. ^1]` and
  ## return match end position + updated environment. If match is
  ## unsuccesful return `startpos` and `none` env, otherwise return
  ## position of the first item *not matched* by pattern.
  # IDEA return more complicated data structure for each match. It
  # might be possible to create something similar to regex101.com
  # where I can see submatches.

  var pos = startpos
  let baseenv = env
  var env = env
  let noRes = (none(TermEnv[V, F]), startpos)

  if pos == elems.len: # Immediately return unification on past-the-end
                       # elements
    if patt.kind in {tpkOptional, tpkZeroOrMore}: # E* and E? can
      # match zero elements, unification succedes regardless of
      # start position
      return (some(env), startpos)
    else:
      return noRes


  mixin exprRepr
  plog:
    echoi level, &"{elems[pos..^1].exprRepr()} {patt.exprRepr()}"

  case patt.kind:
    of tpkTerm:
      let term = patt.term.getIt()
      case getKind(term):
        of tkVariable:
          if env.appendOrUnif(term.name, elems[pos]):
            inc pos
          else:
            return noRes
        of tkPlaceholder:
          inc pos
        of tkConstant:
          let res = unif(term, elems[pos], env, level + 1)
          if res.isSome():
            inc pos
          else:
            return noRes
        of tkFunctor:
          iflet (env = unif(term, elems[pos], env, level + 1)):
            inc pos
          else:
            return noRes
        else:
          raiseAssert(&"#[ IMPLEMENT {getKind(term)} ]#")
    of tpkConcat:
      for subpatt in patt.patterns:
        let (resenv, endpos) = partialMatch(
          elems, pos, subpatt, env, level + 1)

        if resenv.isSome():
          env = resenv.get()
          pos = endpos
        else:
          return noRes

      return (some(env), pos)
    of tpkZeroOrMore:
      while true:
        let (resenv, endpos) = partialMatch(
          elems, pos, patt.patt.getIt(), env, level + 1)

        iflet (tmp = resenv):
          env.mergeEnv tmp
          pos = endpos
        else: # 0+ - always succeds in unification, possibly not
              # producing any shift
          break
    of tpkOptional:
      let (resenv, endpos) = partialMatch(
        elems, pos, patt.patt.getIt(), env, level + 1)

      if resenv.isSome():
        env = resenv.get()
        pos = endpos
    of tpkAlternative:
      block altTries:
        for alt in patt.patterns:
          let (resenv, endpos) = partialMatch(elems, pos, alt, env, level + 1)
          iflet (env = resenv):
            pos = endpos
            break altTries # NOTE no backtracking is performed right
            # now - first matchin alternative at point is accepted
            # each time. Attempts are not resumed if subsequent
            # matches fail.
          else:
            discard

        return noRes
    else:
      raiseAssert("#[ IMPLEMENT ]#")

  plog:
    echoi level, "pt: ", baseenv.exprRepr(), "\e[31m->\e[39m", env.exprRepr()
  return (some(env), pos)

func unif*[V, F](elems: seq[Term[V, F]],
                 patt: TermPattern[V, F],
                 env: TermEnv[V, F] = makeEnvironment[V, F](),
                 level: int,
                 fullMatch: bool = true): Option[TermEnv[V, F]] =
  ## Unify `patt` to elements in `elems` using environment `env`. If
  ## `fullMatch` is true return `some()` environment only if input
  ## sequence matcher completely. Otherwise repeatedly apply pattern
  ## on sequence.
  if fullMatch:
    let (resenv, endpos) = partialMatch(elems, 0, patt, env, level + 1)
    if endpos != elems.len:
      return none(TermEnv[V, F]) # Not matched full pattern
    else:
      return resenv # Matched whole input
  else:
    var env = env
    var pos = 0

    while pos < elems.len:
      # NOTE for now I will assum passing sublist is really cheap. If
      # not - will use linked list or something like that.
      # echov pos
      let (resenv, endpos) = partialMatch(elems, pos, patt, env, level + 1)
      if resenv.isSome():
        if endpos == pos: # null match - return immediately (next
                          # matches will yield the same result)
          return resenv

        env = resenv.get()
        pos = endpos
      else:
        if endpos == 0:
          return none(TermEnv[V, F]) # Not a single match
        else:
          return resenv # At least one match

    return some(env)

func unifLists*[V, F](
  elems1, elems2: seq[Term[V, F]],
  env: TermEnv[V, F], level: int): Option[TermEnv[V, F]] =
  ## Unifty two lists of terms. Each list may contain variables,
  ## constants, other terms and patterns. Pattern matches multiple
  ## elements at once, so unification of `[@a & @a]` and `[1, 2]` will
  ## give `{@a -> [1, 2]}`
  mixin exprRepr
  plog:
    echoi level, elems1.exprRepr(), "=", elems2.exprRepr()

  var
    tmpRes = env
    idx1 = 0
    idx2 = 0

  while (idx1 < elems1.len) and (idx2 < elems2.len):
    let
      el1 = elems1[idx1]
      el2 = elems2[idx2]
      ek1 = el1.getKind()
      ek2 = el2.getKind()

    plog:
      echoi level, &"[{idx1}] :: [{idx2}]"
    if (ek1, ek2) == (tkPattern, tkPattern):
      raiseAssert("#[ IMPLEMENT:ERROR pattern-pattern match ]#")
    elif ek1 == tkPattern: # Unifty list part with pattern
      let (resenv, pos) = partialMatch(
        elems2, idx2, el1.getPatt(), tmpRes, level + 1)

      iflet (res = resenv):
        inc idx1
        idx2 = pos
        # echov res.exprRepr()
        tmpres.mergeEnv res
      else:
        return none(TermEnv[V, F])

    elif ek2 == tkPattern:
      let (resenv, pos) = partialMatch(
        elems1, idx1, el2.getPatt(), tmpRes, level + 1)

      iflet (res = resenv):
        inc idx2
        idx1 = pos
        # echov res.exprRepr()
        tmpres.mergeEnv res
      else:
        return none(TermEnv[V, F])
    else:
      iflet (res = unif(el1, el2, tmpres, level + 1)): # Unift two elements directly
        inc idx1
        inc idx2
        tmpres.mergeEnv res
      else:
        return none(TermEnv[V, F])

  if (idx1 < elems1.len) or (idx2 < elems2.len): # Not full match
    # on either of patterns
    return none(TermEnv[V, F])
  else:
    return some(tmpRes)

  plog:
    defer:
      if result.isSome():
        echoi level, "ls: ", env.exprRepr(), "\e[31m->\e[39m", result.get().exprRepr()
      else:
        echoi level, "list unification failed"

func unifFunctorHeads*[V, F](
  term1, term2: Term[V, F],
  env: TermEnv[V, F], level: int): Option[TermEnv[V, F]] =
  ## Unify two functor heads. Unification of two functors with
  ## predicates is not allowed, everything else is supported. If
  ## functor head uses variable it MUST be bound to functor constant.
  assert term1.tkind == tkFunctor and term2.tkind == tkFunctor
  let noRes = none(TermEnv[V, F])


  if term1.headKind == fhkPredicate or term2.headKind == fhkPredicate:
    if term1.headKind == fhkPredicate and term2.headKind == fhkPredicate:
      raiseAssert("Cannot unifty two functor heads with predicates")

    else:
      var fsym: F
      let ordd: tuple[predc, nonPred: Term[V, F]] =
        block:
          let (predc, nonPred) =
            if term1.headKind == fhkPredicate: (term1, term2)
            else: (term2, term1)

          if nonPred.headKind == fhkVariable:
            let deref = env[nonPred.funcVariable]
            let varstr = nonPred.funcVariable.exprRepr
            if deref.tkind notin {tkConstant, tkFunctor}:
              raiseAssert(msgjoin(
                "Variable", varstr, "is bound to value of kind",
                deref.tkind, "and cannot be unified with functor"))

            if deref.isPredicate:
              raiseAssert(msgjoin(
                "Variable", varstr, "is bound to constant with predicate",
                "and cannot be unified with functor"))

            if not deref.isFunctor:
              raiseAssert(msgjoin(
                "Variable", varstr, "is bound to non-functor value",
                "- cannot substitute it into functor head"))

            fsym = deref.fsym
            (predc, deref)
          else:
            fsym = nonPred.functor
            (predc, nonPred)

      if ordd.predc.funcPred(fsym):
        result = some(env)
        if ordd.predc.bindHead:
          if result.get().appendOrUnif(
            ordd.predc.headVar, makeConstant[V, F](fsym)):
            return
          else:
            return noRes
      else:
        return noRes
  else:
    let
      k1 = term1.headKind
      k2 = term2.headKind

    if (k1, k2) == (fhkVariable, fhkVariable):
      let
        deref1 = env[term1.funcVariable]
        deref2 = env[term2.funcVariable]

      if (not deref1.isFunctor) or (not deref2.isFunctor):
        raiseAssert(msgjoin(
          "Term head is bound to non-functor variable"))

    elif (k1, k2) in [(fhkValue, fhkVariable), (fhkVariable, fhkValue)]:
      let t: tuple[tvar, tval: Term[V, F]] =
        if (k1, k2) == (fhkValue, fhkVariable):
          (term2, term1)
        else:
          (term1, term2)

      if t.tvar in env:
        let deref = env[t.tvar.funcVariable]
        assert deref.isFunctor
        if t.tval.functor == deref.fsym:
           result = some(env)
           if result.get().appendOrUnif(
             t.tvar.funcVariable,
             makeConstant[V, F](deref.getFsym)):
             return
           else:
             return noRes
      else:
        result = some(env)
        if result.get().appendOrUnif(
          t.tvar.funcVariable,
          makeConstant[V, F](t.tval.getFsym)):
          return
        else:
          return noRes



    # elif (k1, k2) == (fhkVariable, fhkValue):
    #   let deref = env[term1.funcVariable]
    #   assert deref.isFunctor
    #   if term2.functor == deref.fsym:
    #      result = some(env)
    #      if result.get().appendOrUnif(term1.funcVariable, term2):
    #        return
    #      else:
    #        return noRes

    else:
      if term1.functor == term2.functor:
        result = some(env)
      else:
        return noRes


func unifConstants*[V, F](
  const1, const2: Term[V, F],
  env: TermEnv[V, F], level: int): Option[TermEnv[V, F]] =
  ## Unify two constants. Unification of two constants with predicates
  ## is not allowed. If one of the constants is a predicate, other
  ## MUST be bound to non-functor value.
  assert const1.tkind == tkConstant and const2.tkind == tkConstant
  let noRes = none(TermEnv[V, F])

  if const1.isPredicate or const2.isPredicate:
    if const1.isPredicate and const2.isPredicate:
      raiseAssert("Cannot unify two predicates")
    else:
      let (predc, val) =
        if const1.isPredicate: (const1, const2) else: (const2, const1)

      if val.isFunctor:
        raiseAssert(msgjoin(
          "Cannot unify functor constant with other predicate.",
          "Attempt to unify (1) constant with predicate and (2)",
          "value of functor kind"
        ))
      else:
        if predc.constPred(val.value):
          result = some(env)
          if predc.bindConst:
            if result.get().appendOrUnif(predc.constVar, val):
              return
            else:
              return noRes
        else:
          return noRes
  else:
    if const1.isFunctor != const2.isFunctor:
      raiseAssert(msgjoin(
        "Cannot compare functor constant with value.",
        "One of the constants containts functor value,",
        "while other does not."
      ))
    else:
      if const1.isFunctor:
        if const1.fsym == const2.fsym:
          return some(env)
        else:
          return noRes
      else:
        if const1.value == const2.value:
          return some(env)
        else:
          return noRes



func unif*[V, F](
  t1, t2: Term[V, F], env: TermEnv[V, F], level: int): Option[TermEnv[V, F]] =
  ## Attempt to unify two terms. On success substitution (environment)
  ## is return for which two terms `t1` and `t2` could be considered
  ## equal.
  ##
  ## - TODO :: Add overload with optional mutable argument for storing
  ##   unification trace in - useful for debugging and general execution
  ##   logging.
  mixin exprRepr
  plog:
    echoi level, t1.exprRepr(), t2.exprRepr()


  if t1.listvarp() or t2.listvarp():
    var env = env
    if t1.listvarp():
      if env.appendOrUnif(t1.getVName(), t2):
        result = some(env)
      else:
        result = none(TermEnv[V, F])
    else:
      if env.appendOrUnif(t2.getVName(), t1):
        result = some(env)
      else:
        result = none(TermEnv[V, F])
  else:
    let
      val1 = dereference(t1, env)
      val2 = dereference(t2, env)
      k1 = getKind(val1)
      k2 = getKind(val2)

    if k1 == tkConstant and k2 == tkConstant:
      return unifConstants(val1, val2, env, level + 1)
      # if val1 == val2:
      #   result = some(env)
      # else:
      #   result = none(TermEnv[V, F])
    elif k1 == tkVariable:
      # result = some(bindTerm(val1, val2, env))
      result = some(env)
      if not result.get().appendOrUnif(val1.getVName(), val2):
        return none(TermEnv[V, F])
    elif k2 == tkVariable:
      result = some(env)
      if not result.get().appendOrUnif(val2.getVName(), val1):
        return none(TermEnv[V, F])
      # result = some(bindTerm(val2, val1, env))
    elif (k1, k2) in @[(tkConstant, tkFunctor), (tkFunctor, tkConstant)]:
      result = none(TermEnv[V, F])
    elif k1 in {tkList, tkPattern}: # list | pattern
      # REFACTOR use `UnificationError` exception instead of just `assert`
      assert (k1, k2) != (tkPattern, tkPattern), # pattern & pattern - die
         "Cannot unify two patterns. Terms has kind 'tkPattern'"

      # REFACTOR `UnificationError`
      assert k2 in {tkList, tkPattern},
         &"Cannot unify list with {k2} only " &
           "pattern-list unification is supported"
      if (k1, k2) == (tkList, tkList): # list-list unification
        result = unifLists(
          val1.getElements(), val2.getElements(), env, level + 1)
      else: # list-pattern unfification
        if k1 == tkList: # k2 is pattern
          result = val1.getElements().unif(
            val2.pattern, env, level + 1, val2.fullMatch)
        else: # k1 is pattern
          result = val2.getElements().unif(
            val1.pattern, env, level + 1, val1.fullMatch)
        # for elem in t1.
    else:
      if (k1 == tkFunctor) and (k2 != tkFunctor) or
         (k2 == tkFunctor) and (k1 != tkFunctor):
        # REFACTOR `UnificationError`
        raiseAssert(msgjoin(
          "Cannot unify functor and non-functor directly. K1 is ", k1,
          " and K2 is ", k2))

      result = unifFunctorHeads(val1, val2, env, level + 1)
      if result.isNone():
        return result

      result = unif(
        val1.getArgumentList(),
        val2.getArgumentList(),
        result.get(), level + 1
      )

  plog:
    if result.isSome():
      echoi level, "mn: ", env.exprRepr(), "\e[31m->\e[39m", result.get().exprRepr()
    else:
      echoi level, "unification failed"

template unifp*[V, F](t1, t2: Term[V, F]): untyped =
  var env {.inject.}: TermEnv[V, F]
  let unifRes = unif(t1, t2, makeEnvironment[V, F](), 0)
  if unifRes.isSome():
    env = unifRes.get()
    true
  else:
    false

iterator redexes*[V, F](
  term: Term[V, F], ): tuple[red: Term[V, F], path: TreePath] =
  ## Iterate over all redex in term
  var que: Deque[(Term[V, F], TreePath)]
  que.addLast((term, @[0]))
  while que.len > 0:
    let (nowTerm, path) = que.popFirst()
    if getKind(nowTerm) == tkFunctor:
      for idx, subTerm in getArguments(nowTerm):
        que.addLast((subTerm, path & @[idx]))

    yield (red: nowTerm, path: path)

func replaceAll*[V, F](
  terms: seq[Term[V, F]], patt: TermPattern[V, F]): seq[Term[V, F]] =
  discard

proc setAtPath*[V, F](term: var Term[V, F], path: TreePath, value: Term[V, F]): void =
  case getKind(term):
    of tkFunctor, tkList:
      if path.len == 1:
        term = value
      else:
        setAtPath(
          term = getNthMod(term, path[1]),
          path = path[1 .. ^1],
          value = value)
    of tkPattern:
      # REFACTOR `UnificationError`
      raiseAssert("Cannot set value at path *inside* pattern")
    of tkVariable:
      term = value
    of tkPlaceholder:
      # REFACTOR `UnificationError`
      assert false, "Cannot assign to placeholder: " & $term & " = " & $value
    of tkConstant:
      term = value
      # assert false, "Cannot assign to constant: " & $term & " = " & $value

func substitute*[V, F](term: Term[V, F], env: TermEnv[V, F]): Term[V, F]
func substElements*[V, F](
  args: seq[Term[V, F]], env: TermEnv[V, F]): seq[Term[V, F]] =
  for arg in args:
    if arg.listvarp(): # Always splice list variables
      for value in env[arg].getElements():
        result.add value.substitute(env)
    else:
      result.add arg.substitute(env)

func substitute*[V, F](term: Term[V, F], env: TermEnv[V, F]): Term[V, F] =
  ## Substitute all variables in term with their values from environment
  case term.getKind():
    of tkConstant:
      return term
    of tkVariable:
      if term.getVName() in env:
        return term.dereference(env)
      else:
        discard # NOTE possible error

    of tkFunctor:
      case term.headKind:
        of fhkValue:
          return makeFunctor(
            term.getFSym(),
            term.getArguments().substElements(env))
        of fhkPredicate:
          raiseAssert("Cannot subsitute head for functor with predicate")
        of fhkVariable:
          if term.getVName() in env:
            let value = env[term.getVName()]
            if not value.functorvalp():
              raiseAssert(msgjoin(
                "Variable", term.getVName(),
                "is bound to non-functor value"))
            else:
              return makeFunctor(
                value.getFSym(), term.getArguments().substElements(env))

    of tkPlaceholder:
      return term
    of tkList:
      return makeList(term.getElements().substElements(env))
    of tkPattern:
      # REFACTOR `SubstitutaionError`
      raiseAssert("#[ Cannot subsitute value into from pattern ]#")

func mergeEnv*[V, F](env: var TermEnv[V, F], other: TermEnv[V, F]): void =
  for vsym, value in other:
    if vsym notin env:
      # env.appendOrUnif(vsym, value)
      env[vsym] = value
    else:
      if vsym.listvarp():
        env[vsym] = value
        # for val in value.getElements():
        #   env[vsym].addElement val
      else:
        discard

func appendOrUnif*[V, F](env: var TermEnv[V, F],
                         vsym: VarSym, value: Term[V, F]): bool =
  ## If variable `vsym` is missing from the environment add it and
  ## return true. If variable is a list `@a` append value and return
  ## true. Otherwise return result of unification for variable value.
  ## Environment `env` is **modified** on success.
  ##
  ## NOTE: in this case list variables behave almost like placeholders
  ## - unification always succeds.
  ##
  ## - `{} + ($a, 12) ==> {$a -> 12}, true`
  ## - `{@a -> [12]} + (@a, 19) ==> {@a -> [12, 19]}, true`
  ## - `{$a -> 12} + ($a, 12) => {$a -> 12}, true`
  ## - `{$a -> 12} + ($a, 19) => {$a -> 12}, false`
  if vsym in env:
    if vsym.isList:
      env[vsym].addElement value
      return true
    else:
      # REVIEW pass `env` instead of making new environment
      return unif(env[vsym], value, makeEnvironment[V, F](), 0).isSome()
  else:
    if vsym.isList:
      env[vsym] = makeList(@[value])
      return true
    else:
      env[vsym] = value
      return true

func match*[V, F](
  redex: Term[V, F],
  matchers: MatcherList[V, F]): Option[TermEnv[V, F]]

func match*[V, F](redex: Term[V, F], matcher: TermMatcher[V, F]): Option[TermEnv[V, F]] =
  # NOTE actually I might have to use full-blown backtracking here:
  # each rule might have one or more nested terms. Rule pair is
  # already almost like a clause. The only difference is (1)
  # additional baggage in form of generator and (2) support for
  # matches that are not terms.
  let unifRes =
    if matcher.isPattern:
      unif(matcher.patt, redex, makeEnvironment[V, F](), 0)
    else:
      matcher.matcher(redex)

  if unifRes.isSome():
    var res: TermEnv[V, F] = unifRes.get()
    for vname, submatch in matcher.subpatts:
      #[ IMPLEMENT check if variable is actually present in environment ]#
      #[ IMPLEMENT check if variable generated from submatch does not overide any of
                   already existing variables
      ]#
      let submRes = match(res[vname], submatch)
      if submRes.isSome():
        res.mergeEnv(submRes.get())

    mixin difference
    if not(res.hasAll(difference(matcher.varlist, matcher.optVars))):
      if matcher.default == nil:
        raiseAssert(msgjoin(
          "Cannot get default value for variables:", res.missingVars(
            matcher.varlist - matcher.optVars
          ), " `default` callback for term matcher is nil"
        ))

      let default: TermEnv[V, F] = matcher.default(res)
      for vname in matcher.varlist:
        if (vname notin res) and (vname notin matcher.optVars):
          if vname notin default:
            raiseAssert(msgjoin(
              "Variable '", vname, "' is missing from default environment. Need to get",
              "values for variables:", res.missingVars(matcher.varlist - matcher.optVars),
              ", but default enviornment provides:", default.varlist()
            ))

          res[vname] = default[vname]

    return some(res)

func match*[V, F](
  redex: Term[V, F],
  matchers: MatcherList[V, F]): Option[TermEnv[V, F]] =
  for id in matchers.first[redex.getSym()] & matchers.forceTry:
    result = match(redex, matchers.patterns[id])
    if result.isSome():
      break

func apply*[V, F](redex: Term[V, F], rule: RulePair[V, F]): Option[TermEnv[V, F]] =
  ## Match pattern from `rule` with `redex` and return unification
  ## environment.
  return match(redex, rule.matchers)
  # for id in rule.first[redex.getSym()] & rule.matchers:
  #   return match(redex, rule.rules[id])

iterator possibleMatches*[V, F](system: RedSystem[V, F], redex: Term[V, F]): RuleId =
  let fsym = redex.getSym()
  for pattId in system.first.getOrDefault(fsym, @[]):
    yield pattId

  for pattId in system.matchers:
    yield pattId

func findApplicable*[V, F](
  system: RedSystem[V, F],
  redex: Term[V, F],
  rs: ReductionState,
  path: TreePath # REVIEW is it necessary?
                         ): Option[(RuleId, TermEnv[V, F], RulePair[V, F])] =
  ## Return first rule in system that can be applied for given `redex`
  ## and unification environment under which rule matches with pattern
  ## in rule.
  for id in system.possibleMatches(redex):
    let rule = system.rules[id]
    let env = redex.apply(rule)
    if env.isSome():
      return some((id, env.get(), rule))

func generate*[V, F](rule: RulePair[V, F], env: TermEnv[V, F]): Term[V, F] =
  ## Apply generator in `rule` using environment `env`
  if rule.gen.isPattern:
    rule.gen.patt.substitute(env)
  else:
    rule.gen.gen(env)

func getNthRule*[V, F](system: RedSystem[V, F], idx: int): RulePair[V, F] =
  system.rules[idx]

template reductionTriggersBFS*[V, F](
  redex: Term[V, F], system: RedSystem[V, F], body: untyped): untyped =

  var rs = ReductionState()
  iterateItBFS(redex, it.getArguments(), it.getKind() == tkFunctor):
    let rule = system.findApplicable(it, rs, rootTreePath)
    if rule.isSome():
      let (ruleId {.inject.}, env {.inject.}, rulePair {.inject.}) = rule.get()
      block:
        body


template reductionTriggersDFS*[V, F](
  redex: Term[V, F], system: RedSystem[V, F], body: untyped): untyped =

  var rs = ReductionState()
  iterateItDFS(redex, it.getArguments(),
               it.getKind() == tkFunctor, dfsPreorder):
    let rule = system.findApplicable(it, rs, rootTreePath)
    if rule.isSome():
      let (ruleId {.inject.}, env {.inject.}, rulePair {.inject.}) = rule.get()
      block:
        body

template matchPattern*[V, F](
  redex: Term[V, F], matcher: TermMatcher[V, F], body: untyped): untyped =
  let env {.inject.} = redex.match(matcher)
  block:
    body


template matchPattern*[V, F](
  redex: Term[V, F], matchers: MatcherList[V, F], body: untyped): untyped =
  let env {.inject.} = redex.match(matchers)
  block:
    body

template matchPattern*[V, F](
  redex: Term[V, F], sys: RedSystem[V, F], body: untyped): untyped =
  let rule {.inject.} = redex.match(matcher)
  block:
    body

func reduce*[V, F](
  term: Term[V, F],
  system: RedSystem[V, F],
  maxDepth: int = 40,
  reduceConstraints: ReduceConstraints = rcApplyOnce
                ): tuple[term: Term[V, F], ok: bool, rewPaths: Trie[int, set[RuleId]]] =
  ##[

Perform reduction of `term` using `system` rules.

Iterate over all subterms (redexes) in `term` and try each reduction
rule in `system`. If rule matches, replace subterm with output of the
rule value generator.

## Parameters

:term: term to reduce
:system: collection of rules (matcher - generator pairs)
:cb: implementation callbacks for term
:maxDepth: do not reduce terms deeper than this value
:reduceConstaints: Configuration for continous application of
                   reduction rules on the same paths.
   - **rcNoConstaints** Reduce as long as reduction can take
     place
   - **rcRewriteOnce** do not rewrite subterm or any of it's
     descendants after it has been reduced once
   - **rcApplyOnce** do not use the same rule on term or any of
     it's descendants after rule has been applied once. Reduction
     of the term (or descendants) might still take place but
     using different rules.

  ]##
  var term = term
  var rs = ReductionState(constr: reduceConstraints, maxDepth: maxDepth)
  defer:
    result.rewPaths = rs.rewPaths

  var canReduce = true
  while canReduce:
    canReduce = false
    for (redex, path) in term.redexes():
      let rule = system.findApplicable(redex, rs, path)
      if rule.isSome():
        canReduce = true
        result.ok = true
        let (idx, env, rule) = rule.get()
        let genRes = rule.generate(env).substitute(env)
        term.setAtPath(path, genRes)

  result.term = term
