$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_a3: the greatest universal lower bound for the average modulus
  of the roots of a degree-2019 polynomial with strictly increasing real
  coefficients between 1 and 2019 is 2019^(-1/2019). This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  A ranges over all real coefficient functions on 0 through 2019. The
  endpoint bounds and strict inequalities make its leading coefficient
  nonzero, so these functions represent exactly the source polynomials of
  degree 2019.

  Z ranges over complex sequences on 0 through 2018. The identity required
  for every complex z says that Z lists all 2019 roots, with multiplicity,
  because the polynomial equals its leading coefficient times the product
  of the corresponding linear factors. Thus the displayed finite sum is
  exactly the source sum of root moduli and is independent of the ordering
  of Z.

  P2019A3Admissible(M) says that M is a lower bound for every admissible
  polynomial and every equivalent root enumeration. The final conjunction
  expands IsGreatest: the annotated value is admissible and every admissible
  real M is at most it. The definition and final declaration are unproved
  $a statement encodings; this database contains no $p proof declaration.
$)

$c P2019A3Admissible $.

p2019a3-admissible-syntax $a wff ( P2019A3Admissible M ) $.

${
  $d A M Z j k z $.

  p2019a3-admissible-definition $a |- (
    ( P2019A3Admissible M )
    <->
    A. A e. ( RR ^m ( 0 ... ( ; ; ; 2 0 1 9 ) ) )
      A. Z e. ( CC ^m ( 0 ... ( ; ; ; 2 0 1 8 ) ) )
        (
          (
            (
              1 <_ ( A ` 0 )
              /\
              ( A ` ( ; ; ; 2 0 1 9 ) ) <_ ( ; ; ; 2 0 1 9 )
            )
            /\
            (
              A. k e. ( 0 ... ( ; ; ; 2 0 1 8 ) )
                ( A ` k ) < ( A ` ( k + 1 ) )
              /\
              A. z e. CC
                (
                  sum_ k e. ( 0 ... ( ; ; ; 2 0 1 9 ) )
                    (
                      ( A ` k )
                      x.
                      ( z ^ k )
                    )
                )
                =
                (
                  ( A ` ( ; ; ; 2 0 1 9 ) )
                  x.
                  prod_ j e. ( 0 ... ( ; ; ; 2 0 1 8 ) )
                    (
                      z
                      -
                      ( Z ` j )
                    )
                )
            )
          )
          ->
          M
          <_
          (
            (
              sum_ j e. ( 0 ... ( ; ; ; 2 0 1 8 ) )
                (
                  abs
                  `
                  ( Z ` j )
                )
            )
            /
            ( ; ; ; 2 0 1 9 )
          )
        )
  ) $.
$}

putnambench-putnam-2019-a3 $a |- (
  (
    P2019A3Admissible
    (
      ( ; ; ; 2 0 1 9 )
      ^c
      (
        -u
        (
          1
          /
          ( ; ; ; 2 0 1 9 )
        )
      )
    )
  )
  /\
  A. M e. RR
    (
      ( P2019A3Admissible M )
      ->
      M
      <_
      (
        ( ; ; ; 2 0 1 9 )
        ^c
        (
          -u
          (
            1
            /
            ( ; ; ; 2 0 1 9 )
          )
        )
      )
    )
) $.
