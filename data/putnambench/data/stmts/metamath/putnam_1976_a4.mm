$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_a4: an irreducible monic rational cubic with an integer
  coefficient pattern and a shifted root of a second integer cubic has
  another root given by one of two rational functions of the original root.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The integers a, b, c, and d and the real number r retain their source
  domains. The displayed real equations are the evaluations at r and r + 1
  of the two source cubics. The matching polynomial over the rational field
  ( CCfld |`s QQ ) is required to belong to the irreducible elements of its
  univariate polynomial ring.

  The source polynomial variables are eliminated by substituting their
  defining equalities. The existential real root s remains inside the
  conclusion, and its two alternatives are exactly -1 / (r + 1) and
  -(r + 1) / r. The final declaration is one unproved $a statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d r s $.

  putnambench-putnam-1976-a4 $a |-
    A. a e. ZZ
      A. b e. ZZ
        A. c e. ZZ
          A. d e. ZZ
            A. r e. RR
              (
                (
                  (
                    (
                      (
                        ( r ^ 3 )
                        +
                        ( a x. ( r ^ 2 ) )
                      )
                      +
                      ( b x. r )
                    )
                    -
                    1
                  )
                  =
                  0
                  /\
                  (
                    (
                      (
                        (
                          3
                          (
                            .g
                            `
                            (
                              mulGrp
                              `
                              (
                                Poly1
                                `
                                ( CCfld |`s QQ )
                              )
                            )
                          )
                          (
                            var1
                            `
                            ( CCfld |`s QQ )
                          )
                        )
                        (
                          +g
                          `
                          (
                            Poly1
                            `
                            ( CCfld |`s QQ )
                          )
                        )
                        (
                          (
                            (
                              algSc
                              `
                              (
                                Poly1
                                `
                                ( CCfld |`s QQ )
                              )
                            )
                            `
                            a
                          )
                          (
                            .r
                            `
                            (
                              Poly1
                              `
                              ( CCfld |`s QQ )
                            )
                          )
                          (
                            2
                            (
                              .g
                              `
                              (
                                mulGrp
                                `
                                (
                                  Poly1
                                  `
                                  ( CCfld |`s QQ )
                                )
                              )
                            )
                            (
                              var1
                              `
                              ( CCfld |`s QQ )
                            )
                          )
                        )
                      )
                      (
                        +g
                        `
                        (
                          Poly1
                          `
                          ( CCfld |`s QQ )
                        )
                      )
                      (
                        (
                          (
                            algSc
                            `
                            (
                              Poly1
                              `
                              ( CCfld |`s QQ )
                            )
                          )
                          `
                          b
                        )
                        (
                          .r
                          `
                          (
                            Poly1
                            `
                            ( CCfld |`s QQ )
                          )
                        )
                        (
                          var1
                          `
                          ( CCfld |`s QQ )
                        )
                      )
                    )
                    (
                      -g
                      `
                      (
                        Poly1
                        `
                        ( CCfld |`s QQ )
                      )
                    )
                    (
                      (
                        algSc
                        `
                        (
                          Poly1
                          `
                          ( CCfld |`s QQ )
                        )
                      )
                      `
                      1
                    )
                  )
                  e.
                  (
                    Irred
                    `
                    (
                      Poly1
                      `
                      ( CCfld |`s QQ )
                    )
                  )
                )
                /\
                (
                  (
                    (
                      ( ( r + 1 ) ^ 3 )
                      +
                      ( c x. ( ( r + 1 ) ^ 2 ) )
                    )
                    +
                    ( d x. ( r + 1 ) )
                  )
                  +
                  1
                )
                =
                0
              )
              ->
              E. s e. RR
                (
                  (
                    (
                      (
                        ( s ^ 3 )
                        +
                        ( a x. ( s ^ 2 ) )
                      )
                      +
                      ( b x. s )
                    )
                    -
                    1
                  )
                  =
                  0
                  /\
                  (
                    s
                    =
                    (
                      ( -u 1 )
                      /
                      ( r + 1 )
                    )
                    \/
                    s
                    =
                    (
                      ( -u ( r + 1 ) )
                      /
                      r
                    )
                  )
                )
  $.
$}
