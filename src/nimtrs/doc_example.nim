{.define(plainStdout).}

import nimtrs/[trscore, trspprint, trsdsl, nimast_trs]
import options

import ../../tests/ast_term

export ast_term

export options
export trscore, trspprint, trsdsl, nimast_trs

template ex*(body: untyped): AstTerm = makeTerm(astImpl, body)

proc exUnif*(term1, term2: AstTerm): void =
  if unifp(term1, term2):
    echo env.exprRepr()
  else:
    echo "Unification failed"

when isMainModule:
  exUnif(ex(Condition($a)), ex(Condition(%!mkLit("hello"))))
