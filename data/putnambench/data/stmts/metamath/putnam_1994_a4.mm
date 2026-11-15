$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_a4: if A, A+B, A+2B, A+3B, and A+4B are invertible
  2 by 2 integer matrices with integer-matrix inverses, then A+5B is
  likewise invertible. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The structure ( ( 0 ..^ 2 ) Mat ZZring ) is the full ring of 2 by 2
  matrices over the integers. Membership in its Unit set means existence
  of a two-sided inverse in that same integer matrix ring, exactly retaining
  the source requirement that the inverse also have integer entries.

  Each multiple kB is expanded as repeated matrix-ring addition, which is
  equal to multiplication by the integer numeral k in this ring. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d A B $.

  putnambench-putnam-1994-a4 $a |-
    A. A e. ( Base ` ( ( 0 ..^ 2 ) Mat ZZring ) )
      A. B e. ( Base ` ( ( 0 ..^ 2 ) Mat ZZring ) )
        (
          (
            A e. ( Unit ` ( ( 0 ..^ 2 ) Mat ZZring ) )
            /\
            (
              (
                A
                ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                B
              )
              e. ( Unit ` ( ( 0 ..^ 2 ) Mat ZZring ) )
              /\
              (
                (
                  A
                  ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                  (
                    B
                    ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                    B
                  )
                )
                e. ( Unit ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                /\
                (
                  (
                    A
                    ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                    (
                      (
                        B
                        ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                        B
                      )
                      ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                      B
                    )
                  )
                  e. ( Unit ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                  /\
                  (
                    A
                    ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                    (
                      (
                        (
                          B
                          ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                          B
                        )
                        ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                        B
                      )
                      ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                      B
                    )
                  )
                  e. ( Unit ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                )
              )
            )
          )
          ->
          (
            A
            ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
            (
              (
                (
                  (
                    B
                    ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                    B
                  )
                  ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                  B
                )
                ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
                B
              )
              ( +g ` ( ( 0 ..^ 2 ) Mat ZZring ) )
              B
            )
          )
          e. ( Unit ` ( ( 0 ..^ 2 ) Mat ZZring ) )
        )
  $.
$}
