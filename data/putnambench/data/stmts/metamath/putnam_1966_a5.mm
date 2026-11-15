$(
  Statement-only formalization of PutnamBench artifact putnam_1966_a5:
  a linear local operator on continuous real-valued functions is pointwise
  multiplication by a continuous real-valued function. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The class ( RR -cn-> RR ) is set.mm's class of continuous functions from
  RR to RR. The operator T is quantified over the full function space from
  real functions to real functions, while its hypotheses restrict its action
  on continuous functions. Locality uses the closed real intervals and
  non-strict endpoint order of the Lean and Rocq sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d T a b f g h r s x $.

  putnambench-putnam-1966-a5 $a |-
    A. T e. ( ( RR ^m RR ) ^m ( RR ^m RR ) )
      (
        (
          (
            A. f e. ( RR -cn-> RR )
              ( T ` f ) e. ( RR -cn-> RR )
            /\
            A. a e. RR A. b e. RR
              A. f e. ( RR -cn-> RR )
                A. g e. ( RR -cn-> RR )
                  ( T `
                    ( x e. RR |->
                      ( ( a x. ( f ` x ) ) + ( b x. ( g ` x ) ) )
                    )
                  )
                  =
                  ( x e. RR |->
                    (
                      ( a x. ( ( T ` f ) ` x ) )
                      +
                      ( b x. ( ( T ` g ) ` x ) )
                    )
                  )
          )
          /\
          A. r e. RR A. s e. RR
            (
              r <_ s
              ->
              A. f e. ( RR -cn-> RR )
                A. g e. ( RR -cn-> RR )
                  (
                    A. x e. ( r [,] s )
                      ( f ` x ) = ( g ` x )
                    ->
                    A. x e. ( r [,] s )
                      ( ( T ` f ) ` x ) = ( ( T ` g ) ` x )
                  )
            )
        )
        ->
        E. h e. ( RR -cn-> RR )
          A. g e. ( RR -cn-> RR )
            ( T ` g )
            =
            ( x e. RR |-> ( ( h ` x ) x. ( g ` x ) ) )
      )
  $.
$}
