$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_b4: the complex determinant of the tie and signed win-loss
  matrices of a 2011-game, 2011-player tournament is a nonnegative integer
  divisible by 2^2010. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ 2011 represents both the games and the players. An
  arbitrary subset G of its Cartesian square is equivalent to the source
  Boolean-valued outcome function: <. g , i >. e. G means that player i
  wins game g.

  For each pair i,j, the displayed matrix entry is the number of games in
  which i and j have the same outcome, plus the imaginary unit times the
  number in which i wins and j loses minus the number in which i loses and
  j wins. Thus this matrix is definitionally T + iW from the source after
  eliminating the uniquely defined T and W parameters. SetMM's maDet over
  CCfld is the complex determinant.

  The witnesses n and k remain existentially quantified natural numbers.
  The equation n = 2^2010 k is exactly natural-number divisibility, while
  n's membership in NN0 states nonnegativity. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d g i j k n s $.

  putnambench-putnam-2011-b4 $a |-
    A. s e.
      ~P
      (
        ( 0 ..^ ; ; ; 2 0 1 1 )
        X.
        ( 0 ..^ ; ; ; 2 0 1 1 )
      )
      E. n e. NN0
        (
          (
            (
              ( ( 0 ..^ ; ; ; 2 0 1 1 ) maDet CCfld )
              `
              (
                i e. ( 0 ..^ ; ; ; 2 0 1 1 ) ,
                j e. ( 0 ..^ ; ; ; 2 0 1 1 ) |->
                  (
                    (
                      #
                      `
                      {
                        g e. ( 0 ..^ ; ; ; 2 0 1 1 ) |
                        (
                          <. g , i >. e. s
                          <->
                          <. g , j >. e. s
                        )
                      }
                    )
                    +
                    (
                      _i
                      x.
                      (
                        (
                          #
                          `
                          {
                            g e. ( 0 ..^ ; ; ; 2 0 1 1 ) |
                            (
                              <. g , i >. e. s
                              /\
                              -. <. g , j >. e. s
                            )
                          }
                        )
                        -
                        (
                          #
                          `
                          {
                            g e. ( 0 ..^ ; ; ; 2 0 1 1 ) |
                            (
                              -. <. g , i >. e. s
                              /\
                              <. g , j >. e. s
                            )
                          }
                        )
                      )
                    )
                  )
              )
            )
            =
            n
          )
          /\
          E. k e. NN0
            n =
              (
                ( 2 ^ ; ; ; 2 0 1 0 )
                x.
                k
              )
        )
  $.
$}
