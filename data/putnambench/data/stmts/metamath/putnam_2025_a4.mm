$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_a4 (putnambench__metamath__putnam_2025_a4): the least
  dimension of 2025 real square matrices whose pairs commute exactly at
  equal, adjacent, or cyclic-endpoint indices is three. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  For k in NN0, 0 ..^ k is the canonical k-element carrier corresponding
  to Fin k, and P25A4Admissible k quantifies internally over the full
  function space of 2025 real k-by-k matrices. RRfld maMul is SetMM's real
  matrix multiplication.

  The quantified implication retains the source restriction i <= j. Under
  that restriction, j - i belonging to {0,1,2024} is written as the
  equivalent three-way disjunction. Thus the biconditional gives exactly
  the required commutation graph, including the two endpoint indices.

  The final conjunction is the explicit IsLeast characterization: dimension
  3 is admissible, and every admissible natural dimension is at least 3.
  Every declaration is an unproved $a statement syntax or definition; this
  database contains no $p proof declaration.
$)

$c P25A4Admissible $.

p25a4-admissible-syntax $a wff ( P25A4Admissible k ) $.

${
  $d A i j k $.

  p25a4-admissible-definition $a |- (
    ( P25A4Admissible k )
    <->
    E. A e.
      (
        (
          RR
          ^m
          ( ( 0 ..^ k ) X. ( 0 ..^ k ) )
        )
        ^m
        ( 0 ..^ ( ; ; ; 2 0 2 5 ) )
      )
      A. i e. ( 0 ..^ ( ; ; ; 2 0 2 5 ) )
        A. j e. ( 0 ..^ ( ; ; ; 2 0 2 5 ) )
          (
            i <_ j
            ->
            (
              (
                (
                  ( A ` i )
                  (
                    RRfld
                    maMul
                    <.
                      ( 0 ..^ k ) ,
                      ( 0 ..^ k ) ,
                      ( 0 ..^ k )
                    >.
                  )
                  ( A ` j )
                )
                =
                (
                  ( A ` j )
                  (
                    RRfld
                    maMul
                    <.
                      ( 0 ..^ k ) ,
                      ( 0 ..^ k ) ,
                      ( 0 ..^ k )
                    >.
                  )
                  ( A ` i )
                )
              )
              <->
              (
                ( j - i ) = 0
                \/
                (
                  ( j - i ) = 1
                  \/
                  ( j - i ) = ( ; ; ; 2 0 2 4 )
                )
              )
            )
          )
  ) $.
$}

putnambench-putnam-2025-a4 $a |- (
  ( P25A4Admissible 3 )
  /\
  A. k e. NN0
    (
      ( P25A4Admissible k )
      ->
      3 <_ k
    )
) $.
