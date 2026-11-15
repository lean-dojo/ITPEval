$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_a1: the number of integer points in the 2011 by 2011
  nonnegative coordinate square that cannot be endpoints of growing spirals.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A path with N steps is represented by a function P on 0 ... N, so it has
  exactly N + 1 integer-coordinate points. Its length function L is defined
  on 0 ..^ N, the step indices. Requiring N >= 2 matches the source's
  requirement of at least three points.

  P11A1Spiral requires P(0) = (0,0), positive integer step lengths, strict
  increase of those lengths, and the successive directions east, north,
  west, and south according to the step index modulo four. P11A1Endpoints
  is the set of endpoints of all such finite paths. Finite function
  sequences and ordered integer pairs are bijectively equivalent to the
  source lists of two-coordinate integer vectors.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P11A1Spiral P11A1Endpoints $.

p11a1-spiral-syntax $a wff ( P11A1Spiral P N L ) $.
p11a1-endpoints-syntax $a class P11A1Endpoints $.

${
  $d L N P i j $.

  p11a1-spiral-definition $a |- (
    ( P11A1Spiral P N L )
    <->
    (
      (
        N e. NN
        /\
        2 <_ N
      )
      /\
      (
        P : ( 0 ... N ) --> ( ZZ X. ZZ )
        /\
        (
          L : ( 0 ..^ N ) --> NN
          /\
          (
            ( P ` 0 ) = <. 0 , 0 >.
            /\
            (
              A. i e. ( 0 ..^ N ) A. j e. ( 0 ..^ N )
                (
                  i < j
                  ->
                  ( L ` i ) < ( L ` j )
                )
              /\
              A. i e. ( 0 ..^ N )
                (
                  (
                    ( i mod 4 ) = 0
                    ->
                    (
                      ( 1st ` ( P ` ( i + 1 ) ) )
                      =
                      ( ( 1st ` ( P ` i ) ) + ( L ` i ) )
                      /\
                      ( 2nd ` ( P ` ( i + 1 ) ) )
                      =
                      ( 2nd ` ( P ` i ) )
                    )
                  )
                  /\
                  (
                    (
                      ( i mod 4 ) = 1
                      ->
                      (
                        ( 1st ` ( P ` ( i + 1 ) ) )
                        =
                        ( 1st ` ( P ` i ) )
                        /\
                        ( 2nd ` ( P ` ( i + 1 ) ) )
                        =
                        ( ( 2nd ` ( P ` i ) ) + ( L ` i ) )
                      )
                    )
                    /\
                    (
                      (
                        ( i mod 4 ) = 2
                        ->
                        (
                          ( 1st ` ( P ` ( i + 1 ) ) )
                          =
                          ( ( 1st ` ( P ` i ) ) - ( L ` i ) )
                          /\
                          ( 2nd ` ( P ` ( i + 1 ) ) )
                          =
                          ( 2nd ` ( P ` i ) )
                        )
                      )
                      /\
                      (
                        ( i mod 4 ) = 3
                        ->
                        (
                          ( 1st ` ( P ` ( i + 1 ) ) )
                          =
                          ( 1st ` ( P ` i ) )
                          /\
                          ( 2nd ` ( P ` ( i + 1 ) ) )
                          =
                          ( ( 2nd ` ( P ` i ) ) - ( L ` i ) )
                        )
                      )
                    )
                  )
                )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d f l n p $.

  p11a1-endpoints-definition $a |- P11A1Endpoints = {
    p e. ( ZZ X. ZZ ) |
    E. n E. f E. l
      (
        ( P11A1Spiral f n l )
        /\
        ( f ` n ) = p
      )
  } $.
$}

putnambench-putnam-2011-a1 $a |- (
  #
  `
  {
    p e. ( ZZ X. ZZ ) |
    (
      (
        0 <_ ( 1st ` p )
        /\
        ( 1st ` p ) <_ ; ; ; 2 0 1 1
      )
      /\
      (
        (
          0 <_ ( 2nd ` p )
          /\
          ( 2nd ` p ) <_ ; ; ; 2 0 1 1
        )
        /\
        -. p e. P11A1Endpoints
      )
    )
  }
) = ; ; ; ; 1 0 0 5 3 $.
