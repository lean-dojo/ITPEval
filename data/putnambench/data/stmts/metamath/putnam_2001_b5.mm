$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_b5: a continuous real function satisfying
  g(g(x)) = a g(x) + b x for real parameters a,b in (0,1/2) is a scalar
  multiple of the identity function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions, and membership in
  ( RR -cn-> RR ) is set.mm's native assertion of global continuity.
  The parameters a and b range over the full open interval (0,1/2), the
  functional equation retains its universal scope over RR, and the scalar c
  remains internally existential.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F a b c x $.

  putnambench-putnam-2001-b5 $a |-
    A. a e. RR
      A. b e. RR
        A. F e. ( RR ^m RR )
          (
            (
              (
                ( 0 < a /\ a < ( 1 / 2 ) )
                /\
                ( 0 < b /\ b < ( 1 / 2 ) )
              )
              /\
              (
                F e. ( RR -cn-> RR )
                /\
                A. x e. RR
                  ( F ` ( F ` x ) )
                  =
                  (
                    ( a x. ( F ` x ) )
                    +
                    ( b x. x )
                  )
              )
            )
            ->
            E. c e. RR
              A. x e. RR
                ( F ` x ) = ( c x. x )
          )
  $.
$}
