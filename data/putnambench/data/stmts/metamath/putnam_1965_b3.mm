$(
  Statement-only formalization of PutnamBench artifact putnam_1965_b3:
  exactly three positive-integer right-triangle side triples, with the legs
  in nondecreasing order, have area equal to twice their perimeter. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A source triple (a,b,c) is represented by set.mm's ordered triple
  <. a , b , c >. = <. <. a , b >. , c >., hence by an element of
  ( ZZ X. ZZ ) X. ZZ. The nested 1st and 2nd projections recover a, b, and c.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  putnambench-putnam-1965-b3 $a
    |- ( # `
      { t e. ( ( ZZ X. ZZ ) X. ZZ ) |
        (
          0 < ( 1st ` ( 1st ` t ) )
          /\
          (
            ( 1st ` ( 1st ` t ) ) <_ ( 2nd ` ( 1st ` t ) )
            /\
            (
              0 < ( 2nd ` t )
              /\
              (
                (
                  (
                    ( 1st ` ( 1st ` t ) ) ^ 2
                  )
                  +
                  (
                    ( 2nd ` ( 1st ` t ) ) ^ 2
                  )
                )
                =
                (
                  ( 2nd ` t ) ^ 2
                )
                /\
                (
                  (
                    (
                      ( 1st ` ( 1st ` t ) )
                      x.
                      ( 2nd ` ( 1st ` t ) )
                    )
                    / 2
                  )
                  =
                  (
                    2 x.
                    (
                      (
                        ( 1st ` ( 1st ` t ) )
                        +
                        ( 2nd ` ( 1st ` t ) )
                      )
                      +
                      ( 2nd ` t )
                    )
                  )
                )
              )
            )
          )
        )
      }
    ) = 3
  $.
$}
