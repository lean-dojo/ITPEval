$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_a6: classification of the continuous real functions satisfying
  f(x) = f(x^2 + c) for a positive real parameter c. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P96A6RTop is the standard topology on the real numbers. All functions f
  are arbitrary total maps from RR to RR. The left side states global
  continuity and the functional equation on every real input.

  The right side expands the source solution definition. For c at most one
  quarter, f is pointwise constant. For c greater than one quarter, the
  restriction of f to the closed interval from zero to c is continuous,
  its endpoint values agree, the functional equation holds on positive
  inputs, and f is even on negative inputs. These two real-order cases are
  exhaustive and disjoint.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

$c P96A6RTop $.

p96a6-real-topology-syntax $a class P96A6RTop $.

p96a6-real-topology-definition $a |- P96A6RTop =
  ( TopOpen ` RRfld )
$.

${
  $d c d f x $.

  putnambench-putnam-1996-a6 $a |-
    A. c e. RR
      A. f e. ( RR ^m RR )
        (
          0 < c
          ->
          (
            (
              f e. ( P96A6RTop Cn P96A6RTop )
              /\
              A. x e. RR
                ( f ` x )
                =
                ( f ` ( ( x ^ 2 ) + c ) )
            )
            <->
            (
              (
                c <_ ( 1 / 4 )
                /\
                E. d e. RR
                  A. x e. RR
                    ( f ` x ) = d
              )
              \/
              (
                ( 1 / 4 ) < c
                /\
                (
                  ( f |` ( 0 [,] c ) )
                  e.
                  (
                    ( P96A6RTop |`t ( 0 [,] c ) )
                    Cn
                    P96A6RTop
                  )
                  /\
                  (
                    ( f ` 0 ) = ( f ` c )
                    /\
                    (
                      A. x e. RR
                        (
                          0 < x
                          ->
                          ( f ` x )
                          =
                          ( f ` ( ( x ^ 2 ) + c ) )
                        )
                      /\
                      A. x e. RR
                        (
                          x < 0
                          ->
                          ( f ` x ) = ( f ` ( -u x ) )
                        )
                    )
                  )
                )
              )
            )
          )
        )
  $.
$}
