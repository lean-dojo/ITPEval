$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_a2: the number of positive ordered integer quadruples for which
  every three-entry least common multiple equals 3^r times 7^s has the stated
  polynomial formula in the positive integers r and s. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  A source ordered quadruple (a,b,c,d) is represented by the nested set.mm
  ordered pair <. <. <. a , b >. , c >. , d >., hence by an element of
  ( ( ( NN X. NN ) X. NN ) X. NN ). The nested 1st and 2nd projections
  recover a, b, c, and d, while membership in NN is exactly the source
  positivity condition.

  The source auxiliary predicate abcdlcm is inlined using set.mm's integer
  lcm operation. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d r s t $.

  putnambench-putnam-1980-a2 $a |- A. r e. NN A. s e. NN
    (
      (
        #
        `
        {
          t e. ( ( ( NN X. NN ) X. NN ) X. NN ) |
            (
              (
                ( ( 3 ^ r ) x. ( 7 ^ s ) )
                =
                (
                  (
                    ( 1st ` ( 1st ` ( 1st ` t ) ) )
                    lcm
                    ( 2nd ` ( 1st ` ( 1st ` t ) ) )
                  )
                  lcm
                  ( 2nd ` ( 1st ` t ) )
                )
              )
              /\
              (
                (
                  ( ( 3 ^ r ) x. ( 7 ^ s ) )
                  =
                  (
                    (
                      ( 1st ` ( 1st ` ( 1st ` t ) ) )
                      lcm
                      ( 2nd ` ( 1st ` ( 1st ` t ) ) )
                    )
                    lcm
                    ( 2nd ` t )
                  )
                )
                /\
                (
                  (
                    ( ( 3 ^ r ) x. ( 7 ^ s ) )
                    =
                    (
                      (
                        ( 1st ` ( 1st ` ( 1st ` t ) ) )
                        lcm
                        ( 2nd ` ( 1st ` t ) )
                      )
                      lcm
                      ( 2nd ` t )
                    )
                  )
                  /\
                  (
                    ( ( 3 ^ r ) x. ( 7 ^ s ) )
                    =
                    (
                      (
                        ( 2nd ` ( 1st ` ( 1st ` t ) ) )
                        lcm
                        ( 2nd ` ( 1st ` t ) )
                      )
                      lcm
                      ( 2nd ` t )
                    )
                  )
                )
              )
            )
        }
      )
      =
      (
        (
          ( 1 + ( 4 x. r ) )
          +
          ( 6 x. ( r ^ 2 ) )
        )
        x.
        (
          ( 1 + ( 4 x. s ) )
          +
          ( 6 x. ( s ^ 2 ) )
        )
      )
    )
  $.
$}
