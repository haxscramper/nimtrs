import sugar, strutils, sequtils, strformat, sets, options
import hmisc/[helpers]
import nimtrs/[trscore, trspprint]

#===========================  implementation  ============================#


func unif*[V, F](t1, t2: Term[V, F]): Option[TermEnv[V, F]] =
  unif(t1, t2, makeEnvironment[V, F](), 0)

type
  TrmKind = enum
    tmkF
    tmkC
    tmkL

  Trm = object
    case kind: TrmKind:
      of tmkF, tmkL:
        subt: seq[Trm]
      of tmkC:
        val: int

func nT(sub: varargs[Trm]): Trm = Trm(kind: tmkF, subt: toSeq(sub))
func nT(val: int): Trm = Trm(kind: tmkC, val: val)
func `==`(lhs, rhs: Trm): bool =
  lhs.kind == rhs.kind and (
    case lhs.kind:
      of tmkC:
        lhs.val == rhs.val
      of tmkF, tmkL:
        subnodesEq(lhs, rhs, subt)
  )

#======================  case term implementation  =======================#

type
  TrmTerm = Term[Trm, TrmKind]
  TrmEnv = TermEnv[Trm, TrmKind]
  TrmSys = RedSystem[Trm, TrmKind]
  TrmGenp = GenProc[Trm, TrmKind]
  TrmDefGenp = DefaultGenProc[Trm, TrmKind]
  TrmRule = RulePair[Trm, TrmKind]
  TrmMatch = TermMatcher[Trm, TrmKind]
  TrmPatt = TermPattern[Trm, TrmKind]

func nOp(subt: varargs[TrmTerm]): TrmTerm =
  makeFunctor[Trm, TrmKind](tmkF, toSeq(subt))

func nList(elems: seq[TrmTerm]): TrmTerm =
  makeList[Trm, TrmKind](elems)

func nVar(n: string, isList: bool = false): TrmTerm =
  makeVariable[Trm, TrmKind](n, isList)


func nPlaceholder(): TrmTerm = makePlaceholder[Trm, TrmKind]()

func nConst(n: Trm): TrmTerm =
  makeConstant(n, n.kind)

func nConst(val: int): TrmTerm = nConst(nT(val))
func nConst(subt: varargs[Trm]): TrmTerm = nConst(nT(subt))

func mkEnv(vals: varargs[tuple[vname: string, val: TrmTerm]]): TrmEnv =
  for (name, val) in vals:
    result[name] = val

const trmImpl* = TermImpl[Trm, TrmKind](
  getSym: (proc(n: Trm): TrmKind = n.kind),
  isFunctorSym: (proc(kind: TrmKind): bool = kind == tmkF),
  makeFunctor: (proc(op: TrmKind, sub: seq[Trm]): Trm = nT(sub)),
  makeList: (proc(sub: seq[Trm]): Trm = Trm(kind: tmkL, subt: sub)),
  getArguments: (proc(n: Trm): seq[Trm] = n.subt),
  valStrGen: (
    proc(n: Trm): string =
      case n.kind:
        of tmkF: $tmkF
        of tmkC: $n.val
        of tmkL: "[" & n.subt.mapIt($it).join(", ") & "]"
  ),
)

proc fromTerm(term: TrmTerm): Trm = term.fromTerm(trmImpl)
proc toTerm(interm: Trm): TrmTerm = interm.toTerm(trmImpl)
proc treeRepr(val: Trm): string = treeRepr(val, trmImpl)
proc treeRepr(val: TrmTerm): string = treeRepr(val, trmImpl)

proc exprRepr(val: TrmEnv | TrmTerm | TrmSys | TrmRule | TrmPatt): string =
  exprRepr(val, trmImpl)

proc exprRepr(elems: seq[TrmTerm]): string =
  elems.mapIt(it.exprRepr()).join(", ").wrap(("[", "]"))

proc makeSystem(rules: varargs[(TrmTerm, TrmTerm)]): TrmSys =
  makeReductionSystem[Trm, TrmKind](
    rules.mapPairs(makeRulePair(
      makeMatcher(lhs),
      makeGenerator(rhs)
    ))
  )

proc makeRule(lhs, rhs: TrmTerm): TrmRule =
  makeRulePair(
    makeMatcher(lhs),
    makeGenerator(rhs)
  )

proc makeSystem(rules: varargs[(TrmMatch, TrmTerm)]): TrmSys =
  makeReductionSystem[Trm, TrmKind](
    rules.mapPairs(makeRulePair(
      lhs, makeGenerator(rhs))))

proc makePatt(
  upper: TrmTerm, subpatts: varargs[(string, TrmTerm)],
  default: TrmDefGenp = nil): TrmMatch =
  makeMatcher(
    upper,
    subpatts.mapPairs((parseVarSym(lhs), rhs)).toPattList(),
    default)


#================================  tests  ================================#

import unittest

proc cmpTerm(term: TrmTerm | Trm, val: Trm | TrmTerm): void =
  let ok =
    (when term is TrmTerm: term.fromTerm() else: term) ==
    (when val is TrmTerm: val.fromTerm() else: val)

  if not ok:
    echo "Found:"
    echo treeRepr(term)
    echo "Expected:"
    echo treeRepr(val)
    raiseAssert("Fail")

suite "Nim trs primitives":
  test "To-from term convesion":
    let t = nT(nT(12), nT(2))
    assert t.toTerm(trmImpl).fromTerm(trmImpl) == t

  test "Variable substitution in env":
    cmpTerm nVar("ii").substitute(mkEnv({
      "ii" : nConst(nT(90))
    })), nT(90)

    cmpTerm nOp(nVar("ii"), nConst(nT(12))).substitute(mkEnv({
      "ii" : nConst(nT(90))
    })), nT(nT(90), nT(12))

    cmpTerm nOp(nOp(nOp(nVar("ii")))).substitute(mkEnv({
      "ii" : nConst(nT(120))
    })), nT(nT(nT(nT(120))))

    cmpTerm nOp(nVar("i1"), nVar("i2"), nVar("i3")).substitute(mkEnv({
      "i1" : nConst(nT(10)),
      "i2" : nConst(nT(20)),
      "i3" : nConst(nT(30)),
    })), nT(nT(10), nT(20), nT(30))

    cmpTerm nOp(nVar("ii"), nOp(nVar("ii"))).substitute(mkEnv({
      "ii" : nConst(nT(10))
    })), nT(nT(10), nT(nT(10)))

  test "{fromTerm} exception":
    try:
      discard nOp(nOp(nVar("ii"))).fromTerm()
      fail()
    except GenException[SubstitutionErrorInfo]:
      let e = getGEx[SubstitutionErrorInfo]
      assertEq e.info.path, @[0, 0, 0]
      assertEq e.info.vname, "ii"

  test "{unif} term unification tests":
     block:
       let res = unif(nVar("ii"), nConst(nT(12))).get()
       cmpTerm res["ii"], nConst(nT(12))

     block:
       let res = unif(nOp(nVar("ii")), nOp(nConst(nT(12)))).get()
       cmpTerm res["ii"], nConst(nT(12))

     block:
       let res = unif(
         nOp(nVar("ii"), nVar("ii")),
         nOp(nConst(nT(12)), nConst(nT(12)))
       ).get()

       cmpTerm res["ii"], nConst(nT(12))

     block:
       let res = unif(
         nOp(nVar("ii"), nConst(nT(12))),
         nOp(nConst(nT(12)), nVar("ii"))
       ).get()

       cmpTerm res["ii"], nConst(nT(12))

     block:
       let res = unif(
         nOp(nVar("ii"), nConst(nT(12)), nVar("zz")),
         nOp(nConst(nT(22)), nVar("qq"), nConst(nT(90)))
       ).get()

       cmpTerm res["ii"], nConst(22)
       cmpTerm res["qq"], nConst(12)
       cmpTerm res["zz"], nConst(90)

     block:
       let res = unif(
         nOp(nVar("ii"), nOp(nVar("io"), nConst(90)), nConst(90)),
         nOp(nConst(90), nOp(nConst(8), nConst(90)), nVar("ii"))
       ).get()

       cmpTerm res["ii"], nConst(90)
       cmpTerm res["io"], nConst(8)

  test "List unification test":
    let res = unif(
      nList(@[nConst(12), nConst(90)]),
      nList(@[nVar("ii"), nVar("oo")])
    ).get()

    cmpTerm res["ii"], nConst(12)
    cmpTerm res["oo"], nConst(90)


  test "Pretty-printing":
    echo makeSystem({
      makePatt(
        nOp(nVar("i1"), nConst(nT(90))),
        {
          "i1" : nConst(nT(20)),
          "i2" : nOp(nVar("i1"), nConst(nT(90))),
        }
      ) : nVar("i1")
    }).exprRepr()

    assertEq nOp(nConst(12), nConst(22)).exprRepr(), "tmkF('12', '22')"
    assertEq mkEnv({"ii" : nConst(nT(10))}).exprRepr(), "{($ii -> '10')}"

    assertEq makeRule(nOp(nVar("i1")), nVar("i1")).exprRepr(),
           "tmkF($i1) ~~> $i1"

    assertEq makeSystem({
      nOp(nVar("i1"), nConst(nT(90))) : nVar("i1")
    }).exprRepr(), "0: tmkF($i1, '90') ~~> $i1"

suite "Pattern matching":
  proc unifTest(list: seq[int],
                patt: (TermPattern[Trm, TrmKind], bool) | TrmTerm,
                expected: openarray[(string, TrmTerm)]): void =

    let resOpt = unif(
      list.mapIt(nConst(it)).nList(),
      when patt is TrmTerm:
        patt
      else:
        makePattern(patt[0], patt[1])
    )

    if resOpt.isNone():
      echo "Unification failed"
      echo "list: ", list
      when patt is TrmTerm:
        echo "pattern: ", patt.exprRepr()
      else:
        echo "pattern: ", patt[0].exprRepr()

      raiseAssert("Fail")
    else:
      let res = resOpt.get()
      echo res.exprRepr()
      for (vname, val) in expected:
        cmpTerm res[vname], val

  test "Patter unification test":
    block:
      let res = unif(
        # Input list is `[12, 22]`
        nList(@[nConst(12), nConst(22)]),
        # Pattern is `@a` - variable can be unified with multiple
        # elements at once.
        makePattern(makeTermP(makeVariable[Trm, TrmKind](
          name = "e",
          isList = true # 'List' variable
        )), false # Match is not full (try to match until the end)
        )
      ).get()

      echo res["@e"].exprRepr()
      cmpTerm res["@e"], # Environment contains variable `e` matched with
                         # list `[12, 22]`
          nList(@[nConst 12, nConst 22])

    block:
      let res = unif(
        # Input list is `[1, 1]`
        nList(@[nconst 1, nconst 1]),
        makePattern(makeTermP(nVar(
          "ii",
          false
        )), false)
      ).get()

      echo res["ii"].exprRepr()
      cmpTerm res["ii"], nConst(1)

  # if true: quit 0

  test "Test proc test":
    unifTest(
      @[ 1, 1 ],
      (makeTermP(nVar("ii", false)), false),
      {
        "ii" : nConst(1)
      }
    )

    unifTest(
      @[12, 22],
      (makeTermP(nVar("e", true)), false),
      {
        "@e" : nList(@[nConst 12, nConst 22])
      }
    )

  test "And pattern match":
    unifTest(
      @[1, 2],
      (makeAndP(@[
        makeTermP nVar("e"),
        makeTermP nVar("z")
      ]), true),
      {
        "e" : nConst(1),
        "z" : nConst(2)
      }
    )

    unifTest(
      @[1, 2],
      nList(@[nVar("e"), nVar("z")]),
      {
        "e" : nConst(1),
        "z" : nConst(2)
      }
    )

  # if true: quit 0

  test "Zero-or-more pattern":
    unifTest(
      @[1, 2, 3, 4, 5],
      # `*(@e & @z)` any number of item /pairs/. Move even items in
      # list `@e` and odd ones into `@z`
      (makeZeroOrMoreP(makeAndP(@[
        makeTermP nVar("e", true),
        makeTermP nVar("z", true)
      ])), false),
      {
        "@e" : nList(@[nConst 1, nConst 3]),
        "@z" : nList(@[nconst 2, nconst 4])
      }
    )

  test "Optional":
    unifTest(
      @[1, 2, 3, 4],
      (makeAndP(@[
        makeTermP nVar("l", true),
        makeOptP makeTermP(nConst 2),
      ]), false),
      {
        "@l" : nList(@[nconst 1, nconst 3, nconst 4])
      }
    )

  test "Extract from functor arguments":
    if true:
      let interm: Trm = nT(nt 1, nt 2, nt 3)
      let pattern: TrmTerm =
        nOp(
          makePattern(
              makeZeroOrMoreP(
                makeTermP nVar("a", islist = true)
              ), fullMatch = true))

      let unifRes = unif(interm.toTerm(), pattern)

      assert unifRes.isSome()

      let res = unifRes.get()
      echo res.exprRepr()
      cmpTerm res["@a"], nList(@[nconst 1, nconst 2, nconst 3])

    if true:
      let interm: Trm = nT(nt 1, nt 2, nt 3, nt 4)
      let pattern: TrmTerm =
        nOp(
          makePattern(
              makeZeroOrMoreP(
                makeAndP(@[
                  makeTermP nVar("a", islist = true),
                  makeTermP nVar("b", islist = true)
                ])
              ), fullMatch = true))

      let unifRes = unif(interm.toTerm(), pattern)

      assert unifRes.isSome()

      let res = unifRes.get()
      echo res.exprRepr()
      cmpTerm res["@a"], nList(@[nconst 1, nconst 3])
      cmpTerm res["@b"], nList(@[nconst 2, nconst 4])

    block:
      let interm: Trm = nT(
        nT(nT(2), nT(3)),
        nT(nT(4), nT(9)),
        nT(nT(8), nT(27)),
        nT(90)
      )

      let pattern: TrmTerm =
        nOp( # `Op( *Op(@a, @b) & c )`
          makePattern( # `*Op(@a, @b) & c`
            makeAndP(@[
              makeZeroOrMoreP( # `*Op(@a, @b)`
                makeTermP nOp( # `Op(@a, @b)`
                  nVar("a", islist = true), # `@a`
                  nVar("b", islist = true)  # `@b`
                )
              ),
              makeTermP nVar("c", islist = false) # `c`
            ]),
            fullMatch = true))

      let unifRes = unif(interm.toTerm(), pattern)
      echo pattern.exprRepr()

      assert unifRes.isSome()

      let res = unifRes.get()
      echo res.exprRepr()

      cmpTerm res["@a"], nList(@[nconst 2, nconst 4, nconst 8])
      cmpTerm res["@b"], nList(@[nconst 3, nconst 9, nconst 27])
      cmpTerm res["c"], nconst(90)


    block:

      let pattern: TrmTerm =
        nOp( # `Op( *Op(a, b) )`
          makePattern( # `*Op(a, b)`
            makeZeroOrMoreP( # `*Op(a, b)`
              makeTermP nOp( # `Op(a, b)`
                nVar("a", islist = false), # `a`
                nVar("b", islist = false)  # `b`
              )
            ),
            fullMatch = true))

      block:
        let interm: Trm = nT(nT(nT(2), nT(3)), nT(nT(2), nT(3)),)
        let unifRes = unif(interm.toTerm(), pattern)
        assert unifRes.isSome()
        let res = unifRes.get()

        cmpTerm res["a"], nconst 2
        cmpTerm res["b"], nconst 3

      block:
        let interm: Trm = nT(
          nT(nT(2), nT(3) #[ first binding for `a` ]#),
          nT(nT(2), nT(4) #[ second bindin for `a` - will fail because
                          #`3 != 4` ]#)
        )
        let unifRes = unif(interm.toTerm(), pattern)
        assert unifRes.isNone()


suite "Nim trs reduction rule search":
  test "Rewrite constant":
    let (term, ok, _) = nConst(12).reduce(makeSystem({
      nConst(12) : nConst(14)
    }))

    cmpTerm term, nConst(14)

  test "Rewrite term completely":
    let (term, ok, _) = nConst(nT(nT(12), nT(22))).reduce(makeSystem({
      nConst(nT(nT(12), nT(22))) : nConst(nT(90))
    }))

    cmpTerm term, nConst(90)

  test "Rewrite upper term":
    let (term, ok, _) = (
      nT( nT(120), nT(90)).toTerm()
    ).reduce(makeSystem({
      nOp(nVar("i1"), nConst(nT(90))) : nVar("i1")
    }))

    cmpTerm term, nConst(120)
    assert ok

  test "Rewrite with subpatterms":
    let (term, ok, _) = (
      nT( nT(120), nT(90)).toTerm()
    ).reduce(makeSystem({
      nOp(nVar("i1"), nConst(nT(90))) : nVar("i1")
    }))

  test "Pattern with submatches":
    block:
      let subpatts = {
        "ii" : nOp(nConst(80), nVar("zz"))
      }.toPattList()

      let vars = subpatts.getExportedVars()
      assert "zz" in vars

    block:
      let patt = makePatt(
        nOp(nConst(10), nVar("ii")),
        {
          "ii" : nOp(nConst(80), nVar("zz"))
        }
      )

      let vars = patt.exportedVars()
      assert "ii" in vars # Exported by toplevel matcher
      assert "zz" in vars # Exported by submatcher on `"ii"`

  test "Rewrite system with multiple nested paterns":
    let sys = makeSystem({
      makePatt(nOp(nConst(10), nVar("ii"))) : nOp(nVar("ii")),
      makePatt(
        nOp(nConst(90), nVar("ii"), nVar("uu")), {
          "ii" : nOp(nConst(10), nVar("zz")),
          "uu" : nOp(nConst(20), nVar("ee"))
      }) : nOp(nVar("uu"), nVar("ee")),
      makePatt(nOp(nConst(120), nVar("qq"))) : nConst(90)
    })

    assertEq sys.exprRepr(),
        """
        0: tmkF('10', _ii)      ~~> tmkF(_ii)
        1: tmkF('90', _ii, _uu) ~~> tmkF(_uu, _ee)
           uu: tmkF('20', _ee)
           ii: tmkF('10', _zz)
        2: tmkF('120', _qq)     ~~> '90'""".dedent()

    block:
      # Test rewrite for last rule.
      let res = nT(nT(120), nT(20)).toTerm().reduce(sys)
      assert res.ok
      cmpTerm res.term, nT(90)

    block:
      # Extract variable from nested term
      for val in @[10, 20, 30, 40]:
        let res = nT(nT(10), nT(val)).toTerm().reduce(sys)
        assert res.ok
        cmpTerm res.term, nT(nT(val))

    block:
      let redex = nT(
        nT(90),
        nT(nT(10), nT(666)), # `ii: tmkF('10', _zz)`
        nT(nT(20), nT(777))  # `uu: tmkF('20', _ee)`
      ).toTerm()

      block:
        # Apply rules manually
        for i in 0 .. 2:
          let envres = redex.apply(sys.getNthRule(i))
          if i == 1:
            assert envres.isSome()
            let env = envres.get()

            cmpTerm nT(nT(10), nT(666)), env["ii"]
            cmpTerm nT(nT(20), nT(777)), env["uu"]
            cmpTerm nT(777), env["ee"]

            assertEq env.exprRepr(),
              """
              {
                _zz -> '666'
                _uu -> tmkF('20', '777')
                _ii -> tmkF('10', '666')
                _ee -> '777'
              }""".dedent


  test "Reduction system event-driven iteration":
    let redex = nT(nT(10), nT(20)).toTerm()
    let sys = makeSystem({
      makePatt(nConst(10)) : nConst(-1),
      makePatt(nConst(20)) : nConst(-2),
    })

    # BFS/DFS trigger loops are iterative - all local variables can be
    # accessed without use of `{.global.}` pragma.
    block:
      var localVar: int = 0
      reductionTriggersBFS(redex, sys):
        assert it is TrmTerm
        assert env is TrmEnv
        assert ruleId is RuleId

        case ruleId:
          of 0:
            cmpTerm(it, nT(10))
            inc localVar
          of 1:
            cmpTerm(it, nT(20))
            inc localVar
          else:
            fail()

      assert localVar == 2

    block:
      var localVar: int = 0
      reductionTriggersDFS(redex, sys):
        assert it is TrmTerm
        assert env is TrmEnv
        assert ruleId is RuleId

        case ruleId:
          of 0:
            cmpTerm(it, nT(10))
            inc localVar
          of 1:
            cmpTerm(it, nT(20))
            inc localVar
          else:
            fail()

      assert localVar == 2

  test "{matchPattern} extract data from term":
    type
      U = object
        lhs, rhs: int

    let term = nT(nT(20), nT(30)).toTerm()
    let patt = makePatt(nOp(nVar("lhs"), nVar("rhs")))
    let res: U = term.matchPattern(patt):
      assert env is Option[TrmEnv]
      if env.isSome():
        let env = env.get()
        U(
          lhs: env["lhs"].fromTerm().val,
          rhs: env["rhs"].fromTerm().val
        )
      else:
        U()

    assert res.lhs == 20
    assert res.rhs == 30

  test "{matchPattern} submatchers with default generator":
    type
      U = object
        lhs, rhs: int
        order: (int, int)

    let term = nT(nT(20), nT(30)).toTerm()
    let matcher = makeMatcher(@[
      makePatt(nOp(nVar("lhs"), nVar("rhs"))),
      makePatt(
        nOp(nVar("lhs"), nVar("rhs"), nVar("order")),
        {
          "order": nOp(nVar("ord0"), nVar("ord1"))
        }
      )],
      proc(env: TrmEnv): TrmEnv =
        result["ord0"] = nConst(4)
        result["ord1"] = nConst(6)
      ,
      @["order".parseVarSym()]
    )

    let res: U = term.matchPattern(matcher):
      if env.isSome():
        let env = env.get()
        U(
          lhs: env["lhs"].fromTerm().val,
          rhs: env["rhs"].fromTerm().val,
          order: (
            env["ord0"].fromTerm().val,
            env["ord1"].fromTerm().val
          )
        )
      else:
        U()

    assertEq res, U(lhs: 20, rhs: 30, order: (4, 6))
