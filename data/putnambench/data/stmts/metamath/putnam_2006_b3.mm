$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_b3: the maximum number of unordered linear partitions of an
  n-point subset of the real plane is the binomial coefficient n choose 2
  plus one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P06B3Plane is the real plane represented by ordered pairs. For a subset S,
  P06B3LinearPartitions(S) consists of the two-element families {A,B} of
  subsets of S whose members are disjoint, cover S, and lie strictly on
  opposite sides of a nondegenerate affine line. This includes partitions
  with an empty part.

  The general equation a*x+b*y+c=0 includes vertical lines. On a finite set,
  it is equivalent to the source's graph-line encoding because a separating
  line can be perturbed without crossing any point. The final conjunction
  expands IsGreatest into attainment of the stated value and a universal
  upper bound. Every $a declaration is an unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c P06B3Plane P06B3LinearPartitions $.

p06b3-plane-syntax $a class P06B3Plane $.
p06b3-linear-partitions-syntax $a class P06B3LinearPartitions $.

p06b3-plane-definition $a |- P06B3Plane = ( RR X. RR ) $.

${
  $d A B S T a b c p $.

  p06b3-linear-partitions-definition $a |- P06B3LinearPartitions =
    ( S e. ~P P06B3Plane |->
      {
        T e. ~P ( ~P S ) |
          (
            ( # ` T ) = 2
            /\
            E. A e. T
              E. B e. T
                (
                  A =/= B
                  /\
                  (
                    ( A u. B ) = S
                    /\
                    (
                      ( A i^i B ) = (/)
                      /\
                      E. a e. RR
                        E. b e. RR
                          E. c e. RR
                            (
                              (
                                a =/= 0
                                \/
                                b =/= 0
                              )
                              /\
                              (
                                A. p e. A
                                  0
                                  <
                                  (
                                    (
                                      ( a x. ( 1st ` p ) )
                                      +
                                      ( b x. ( 2nd ` p ) )
                                    )
                                    +
                                    c
                                  )
                                /\
                                A. p e. B
                                  (
                                    (
                                      ( a x. ( 1st ` p ) )
                                      +
                                      ( b x. ( 2nd ` p ) )
                                    )
                                    +
                                    c
                                  )
                                  <
                                  0
                              )
                            )
                    )
                  )
                )
          )
      }
    )
  $.
$}

${
  $d S n $.

  putnambench-putnam-2006-b3 $a |-
    A. n e. NN
      (
        E. S e. ~P P06B3Plane
          (
            ( # ` S ) = n
            /\
            (
              #
              `
              ( P06B3LinearPartitions ` S )
            )
            =
            ( ( n _C 2 ) + 1 )
          )
        /\
        A. S e. ~P P06B3Plane
          (
            ( # ` S ) = n
            ->
            (
              #
              `
              ( P06B3LinearPartitions ` S )
            )
            <_
            ( ( n _C 2 ) + 1 )
          )
      )
  $.
$}
