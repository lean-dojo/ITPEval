$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_a1: classification of the possible real ranges of bivariate
  polynomials with real coefficients. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 2o is the two-element variable-index set. Thus
  ( 2o mPoly RRfld ) is set.mm's ring of finite-support bivariate
  polynomials over the real field, and ( 2o eval RRfld ) evaluates such a
  polynomial at every assignment from 2o to RR.

  The left side is the set of ranges of all these polynomials. The right side
  consists exactly of all real singletons, closed upper rays, closed lower
  rays, open lower rays, open upper rays, and the whole real line, matching
  the solution specified by the ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d S f x z $.

  putnambench-putnam-1969-a1 $a |- (
    {
      S e. ~P RR |
      E. f e. ( Base ` ( 2o mPoly RRfld ) )
        S = ran ( ( 2o eval RRfld ) ` f )
    }
    =
    {
      S e. ~P RR |
      (
        E. x e. RR
          (
            S = { x }
            \/
            (
              S = { z e. RR | x <_ z }
              \/
              (
                S = { z e. RR | z <_ x }
                \/
                (
                  S = { z e. RR | z < x }
                  \/
                  S = { z e. RR | x < z }
                )
              )
            )
          )
        \/
        S = RR
      )
    }
  ) $.
$}
