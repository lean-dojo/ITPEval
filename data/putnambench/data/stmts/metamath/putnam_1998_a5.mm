$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_a5: a finite family of positive-radius open discs covering a
  set in the real plane has a pairwise disjoint subcollection whose
  triple-radius discs still cover the set. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P98A5R2 is the real coordinate plane, P98A5Dist is Euclidean distance,
  and P98A5Ball is the corresponding open ball. The carrier 0 ..^ k has
  exactly k elements and represents Fin k.

  The functions c and r give every center and positive radius on that
  carrier, while e ranges over arbitrary subsets of the plane. The witness
  t is a total selection from 0 ..^ n into the original carrier. Its
  selected open balls are pairwise disjoint, and the union of the selected
  balls after multiplying every radius by three contains e. This is the
  finite-index formulation common to the Lean and Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P98A5I P98A5R2 P98A5Dist P98A5Ball $.

p98a5-index-syntax $a class P98A5I $.
p98a5-plane-syntax $a class P98A5R2 $.
p98a5-distance-syntax $a class ( P98A5Dist A B ) $.
p98a5-ball-syntax $a class ( P98A5Ball A B ) $.

p98a5-index-definition $a |- P98A5I = ( 1 ... 2 ) $.

p98a5-plane-definition $a |- P98A5R2 = ( RR ^m P98A5I ) $.

${
  $d A B j $.

  p98a5-distance-definition $a |- (
    P98A5Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P98A5I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B x $.

  p98a5-ball-definition $a |- (
    P98A5Ball A B
  ) = {
    x e. P98A5R2 |
      ( P98A5Dist A x ) < B
  } $.
$}

${
  $d c e i j k n r t $.

  putnambench-putnam-1998-a5 $a |-
    A. k e. NN0
    A. c e. ( P98A5R2 ^m ( 0 ..^ k ) )
    A. r e. ( RR ^m ( 0 ..^ k ) )
    A. e e. ~P P98A5R2
      (
        (
          A. i e. ( 0 ..^ k ) 0 < ( r ` i )
          /\
          e C_
            U_ i e. ( 0 ..^ k )
              ( P98A5Ball ( c ` i ) ( r ` i ) )
        )
        ->
        E. n e. NN0
          E. t e. ( ( 0 ..^ k ) ^m ( 0 ..^ n ) )
            (
              n <_ k
              /\
              (
                A. i e. ( 0 ..^ n )
                  A. j e. ( 0 ..^ n )
                    (
                      i =/= j
                      ->
                      (
                        (
                          P98A5Ball
                            ( c ` ( t ` i ) )
                            ( r ` ( t ` i ) )
                        )
                        i^i
                        (
                          P98A5Ball
                            ( c ` ( t ` j ) )
                            ( r ` ( t ` j ) )
                        )
                      )
                      =
                      (/)
                    )
                /\
                e C_
                  U_ i e. ( 0 ..^ n )
                    (
                      P98A5Ball
                        ( c ` ( t ` i ) )
                        ( 3 x. ( r ` ( t ` i ) ) )
                    )
              )
            )
      )
  $.
$}
