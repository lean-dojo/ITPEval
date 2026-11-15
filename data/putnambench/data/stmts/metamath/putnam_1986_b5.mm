$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_b5: the assertion that every real polynomial self-map preserving
  x^2 + y^2 + z^2 + xyz is a permutation of the coordinate polynomials with
  zero or two minus signs is false. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 3o is the three-element variable-index set. Thus
  ( 3o mPoly RRfld ) is set.mm's ring of arbitrary finite-support
  polynomials in three variables over the real field, ( 3o eval RRfld )
  evaluates such a polynomial at an assignment in ( RR ^m 3o ), and
  ( 3o mVar RRfld ) gives the three coordinate polynomials.

  The antecedent inlines preservation of
  f(x,y,z) = x^2 + y^2 + z^2 + xyz at every real triple. The four set
  equalities are exactly membership of {p,q,r} in the source set perms;
  unordered triple equality retains all coordinate permutations. The outer
  negation is the source biconditional with its specified solution False.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a p q r $.

  putnambench-putnam-1986-b5 $a |- -.
    A. p e. ( Base ` ( 3o mPoly RRfld ) )
      A. q e. ( Base ` ( 3o mPoly RRfld ) )
        A. r e. ( Base ` ( 3o mPoly RRfld ) )
          (
            A. a e. ( RR ^m 3o )
              (
                (
                  (
                    (
                      (
                        ( ( ( 3o eval RRfld ) ` p ) ` a )
                        ^
                        2
                      )
                      +
                      (
                        ( ( ( 3o eval RRfld ) ` q ) ` a )
                        ^
                        2
                      )
                    )
                    +
                    (
                      ( ( ( 3o eval RRfld ) ` r ) ` a )
                      ^
                      2
                    )
                  )
                  +
                  (
                    (
                      ( ( ( 3o eval RRfld ) ` p ) ` a )
                      x.
                      ( ( ( 3o eval RRfld ) ` q ) ` a )
                    )
                    x.
                    ( ( ( 3o eval RRfld ) ` r ) ` a )
                  )
                )
                =
                (
                  (
                    (
                      ( ( a ` 0 ) ^ 2 )
                      +
                      ( ( a ` 1 ) ^ 2 )
                    )
                    +
                    ( ( a ` 2 ) ^ 2 )
                  )
                  +
                  (
                    (
                      ( a ` 0 )
                      x.
                      ( a ` 1 )
                    )
                    x.
                    ( a ` 2 )
                  )
                )
              )
            ->
            (
              { p , q , r }
              =
              {
                ( ( 3o mVar RRfld ) ` 0 ) ,
                ( ( 3o mVar RRfld ) ` 1 ) ,
                ( ( 3o mVar RRfld ) ` 2 )
              }
              \/
              (
                { p , q , r }
                =
                {
                  ( ( 3o mVar RRfld ) ` 0 ) ,
                  (
                    ( -g ` ( 3o mPoly RRfld ) )
                    `
                    ( ( 3o mVar RRfld ) ` 1 )
                  ) ,
                  (
                    ( -g ` ( 3o mPoly RRfld ) )
                    `
                    ( ( 3o mVar RRfld ) ` 2 )
                  )
                }
                \/
                (
                  { p , q , r }
                  =
                  {
                    (
                      ( -g ` ( 3o mPoly RRfld ) )
                      `
                      ( ( 3o mVar RRfld ) ` 0 )
                    ) ,
                    ( ( 3o mVar RRfld ) ` 1 ) ,
                    (
                      ( -g ` ( 3o mPoly RRfld ) )
                      `
                      ( ( 3o mVar RRfld ) ` 2 )
                    )
                  }
                  \/
                  { p , q , r }
                  =
                  {
                    (
                      ( -g ` ( 3o mPoly RRfld ) )
                      `
                      ( ( 3o mVar RRfld ) ` 0 )
                    ) ,
                    (
                      ( -g ` ( 3o mPoly RRfld ) )
                      `
                      ( ( 3o mVar RRfld ) ` 1 )
                    ) ,
                    ( ( 3o mVar RRfld ) ` 2 )
                  }
                )
              )
            )
          )
  $.
$}
