$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_b6: the largest real bound for a hyperbolic-sine inequality
  between positive real numbers is the absolute logarithm of their ratio.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive real bases, exp(x log(a)) and exp((1-x) log(b)) are exactly
  the real powers a^x and b^(1-x) used by the sources. The two conjuncts
  expand IsGreatest: the explicit value |log(a/b)| satisfies the inequality
  for every permitted real u and x, and every real c satisfying the same
  universal condition is at most that value.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c u x $.

  putnambench-putnam-1991-b6 $a |- A. a e. RR A. b e. RR
    (
      (
        0 < a
        /\
        0 < b
      )
      ->
      (
        A. u e. RR
          (
            (
              0 < ( abs ` u )
              /\
              ( abs ` u )
                <_
                ( abs ` ( log ` ( a / b ) ) )
            )
            ->
            A. x e. RR
              (
                (
                  0 < x
                  /\
                  x < 1
                )
                ->
                (
                  (
                    ( exp ` ( x x. ( log ` a ) ) )
                    x.
                    (
                      exp
                      `
                      (
                        ( 1 - x )
                        x.
                        ( log ` b )
                      )
                    )
                  )
                  <_
                  (
                    (
                      a
                      x.
                      (
                        ( sinh ` ( u x. x ) )
                        /
                        ( sinh ` u )
                      )
                    )
                    +
                    (
                      b
                      x.
                      (
                        ( sinh ` ( u x. ( 1 - x ) ) )
                        /
                        ( sinh ` u )
                      )
                    )
                  )
                )
              )
          )
        /\
        A. c e. RR
          (
            (
              A. u e. RR
                (
                  (
                    0 < ( abs ` u )
                    /\
                    ( abs ` u ) <_ c
                  )
                  ->
                  A. x e. RR
                    (
                      (
                        0 < x
                        /\
                        x < 1
                      )
                      ->
                      (
                        (
                          ( exp ` ( x x. ( log ` a ) ) )
                          x.
                          (
                            exp
                            `
                            (
                              ( 1 - x )
                              x.
                              ( log ` b )
                            )
                          )
                        )
                        <_
                        (
                          (
                            a
                            x.
                            (
                              ( sinh ` ( u x. x ) )
                              /
                              ( sinh ` u )
                            )
                          )
                          +
                          (
                            b
                            x.
                            (
                              ( sinh ` ( u x. ( 1 - x ) ) )
                              /
                              ( sinh ` u )
                            )
                          )
                        )
                      )
                    )
                )
            )
            ->
            c <_ ( abs ` ( log ` ( a / b ) ) )
          )
      )
    )
  $.
$}
