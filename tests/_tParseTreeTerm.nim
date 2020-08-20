# WIP
import sugar, strutils, sequtils, strformat, options
import nimtrs/[trscore, trspprint, trsdsl, parsetree_trs]
import hparse, hparse/llstar_gen

#===========================  implementation  ============================#

#================================  tests  ================================#

import unittest

# TODO deal with type alias in the `initcalls`
type
  ExImpl = TermImpl[ParseTree[NoCategory, string, void], string]
  ExTok = Token[NoCategory, string, void]
  ExTree = ParseTree[NoCategory, string, void]



let impl = initPTreeImpl[NoCategory, string, void]()


proc cmpTerm*(term: Term | ParseTree, val: Term | ParseTree): void =
  let ok =
    (when term is Term: term.fromTerm(impl) else: term) ==
    (when val is Term: val.fromTerm(impl) else: val)

  if not ok:
    echo "Found:"
    echo treeRepr(term, impl)
    echo "Expected:"
    echo treeRepr(val, impl)
    raiseAssert("Fail")

template transformTest*(body: untyped, termIn, termOut: typed): untyped =
  let termIn1 = termIn.toTerm(impl)
  let termRes = matchWith(termIn1, impl):
    body

  if termRes.isSome():
    let res = termRes.get().fromTerm(impl)
    cmpTerm res, termOut
  else:
    echo "input:\n", termIn1.exprRepr(impl)
    echo "expected:\n", termOut.toTerm(impl).exprRepr(impl)
    fail()


template testparse(tokens, grammarBody: untyped): untyped =
  block:
    const defaultCategory {.inject.} = catNoCategory
    const grammarConst =
      block:
        initGrammarCalls(NoCategory, string)
        initGrammarImpl(grammarBody)

    let recParser = newLLStarParser[NoCategory, string, void](
      grammarConst)
    var stream = makeTokens(tokens).makeStream()
    let recTree = recParser.parse(stream)

    recTree


suite "Parse tree rewriting":

  proc makeToken(s: string): ExTok =
    makeToken[NoCategory, string, void](catNoCategory, s)

  proc makeTree(s: string): ExTree = newTree(makeToken(s))

  test "test":
    let tree = @["(", "&", "|", "+", "&", ")"].testparse:
      A ::= !"(" & @*B & !")"
      B ::= [[ it in ["&", "+", "|"] ]]

    echo tree.treeRepr()
    let term = tree.toTerm(impl)
    echo term.exprRepr(impl)

    transformTest do:
      "A"( *"B"( %!makeTree[@a]("&") | _ ) ) => "Z"(@a)
    do:
      tree
    do:
      newTree("Z", @[ makeTree("&"), makeTree("&") ])
