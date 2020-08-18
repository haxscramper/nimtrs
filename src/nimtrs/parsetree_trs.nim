import hparse
import trscore

type
  PTreeTerm*[C, L, I] =
    Term[ParseTree[C, L, I], NTermSym]

  PTreeReduction*[C, L, I] =
    RedSystem[ParseTree[C, L, I], NTermSym]

  PTreeMatcher*[C, L, I] =
    TermMatcher[ParseTree[C, L, I], NTermSym]

  PTreeEnv*[C, L, I] =
    TermEnv[ParseTree[C, L, I], NTermSym]

func initPTreeImpl*[C, L, I](): TermImpl[ParseTree[C, L, I], NTermSym] =
  TermImpl[ParseTree[C, L, I], NTermSym](
    getsym: (
      proc(n: ParseTree[C, L, I]): NTermSym =
        if n.isToken:
          ""
        else:
          n.nterm
    ),
    isFunctorSym: (
      proc(kind: NTermSym): bool =
        kind.len > 0
    ),
    makeFunctor: (
      proc(op: NTermSym,
           sub: seq[ParseTree[C, L, I]]): ParseTree[C, L, I] =
        newTree(op, sub)
    ),
    getArguments: (
      proc(n: ParseTree[C, L, I]): seq[ParseTree[C, L, I]] =
        n.getSubnodes()
    ),
    valStrGen: (
      proc(n: ParseTree[C, L, I]): string =
        n.lispRepr()
    ),
  )
