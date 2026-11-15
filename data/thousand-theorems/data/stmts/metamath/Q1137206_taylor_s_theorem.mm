$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1137206
  (thousand-theorems__metamath__Q1137206), "Taylor's theorem": the Lagrange
  and Cauchy forms of the remainder for the Taylor polynomial of a real
  function on a closed interval, under the source relative smoothness
  hypotheses. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1137206Icc and Q1137206Ioo are the closed and open real intervals from the
  first endpoint to the second. Q1137206Iter is SetMM's relative iterated
  derivative of the restricted function, and Q1137206Taylor is the degree-N
  Taylor polynomial at the first endpoint, evaluated at the second.

  Q1137206Smooth states exactly the two source regularity assumptions: the
  restricted function is C^N on the closed interval, and its N-th relative
  derivative is differentiable at every point of the open interval. The two
  final $a declarations are the Lagrange and Cauchy remainder statements.
  Every preceding $a declaration is syntax or a faithful definition.
$)

$c Q1137206Icc Q1137206Ioo Q1137206Iter Q1137206Taylor
   Q1137206Smooth $.

q1137206-icc-syntax $a class ( Q1137206Icc A X ) $.
q1137206-ioo-syntax $a class ( Q1137206Ioo A X ) $.
q1137206-iter-syntax $a class ( Q1137206Iter F A X N ) $.
q1137206-taylor-syntax $a class ( Q1137206Taylor F A X N ) $.
q1137206-smooth-syntax $a wff ( Q1137206Smooth F A X N ) $.

${
  $d t A $.
  $d t X $.

  q1137206-icc-definition $a |- ( Q1137206Icc A X ) =
    { t e. RR | ( A <_ t /\ t <_ X ) } $.
$}

${
  $d t A $.
  $d t X $.

  q1137206-ioo-definition $a |- ( Q1137206Ioo A X ) =
    { t e. RR | ( A < t /\ t < X ) } $.
$}

q1137206-iter-definition $a |- ( Q1137206Iter F A X N ) =
  (
    (
      ( Q1137206Icc A X )
      Dn
      ( F |` ( Q1137206Icc A X ) )
    )
    ` N
  ) $.

${
  $d k A $.
  $d k F $.
  $d k N $.
  $d k X $.

  q1137206-taylor-definition $a |- ( Q1137206Taylor F A X N ) =
    sum_ k e. ( 0 ... N )
      (
        (
          ( ( Q1137206Iter F A X k ) ` A )
          /
          ( ! ` k )
        )
        x.
        ( ( X - A ) ^ k )
      ) $.
$}

q1137206-smooth-definition $a |- (
  ( Q1137206Smooth F A X N )
  <->
  (
    (
      F |` ( Q1137206Icc A X )
    )
    e.
    (
      (
        C^n ` ( Q1137206Icc A X )
      )
      ` N
    )
    /\
    (
      ( Q1137206Ioo A X )
      C_
      dom
        (
          ( Q1137206Ioo A X )
          _D
          (
            ( Q1137206Iter F A X N )
            |`
            ( Q1137206Ioo A X )
          )
        )
    )
  )
) $.

${
  $d a c f n x $.

  thousand-theorems-metamath-Q1137206-taylor-mean-remainder-lagrange $a |-
    A. a e. RR
      A. x e. RR
        A. n e. NN0
          A. f e. ( RR ^m RR )
            (
              (
                a < x
                /\
                ( Q1137206Smooth f a x n )
              )
              ->
              E. c e. ( Q1137206Ioo a x )
                (
                  ( f ` x )
                  -
                  ( Q1137206Taylor f a x n )
                )
                =
                (
                  (
                    (
                      ( Q1137206Iter f a x ( n + 1 ) )
                      ` c
                    )
                    x.
                    ( ( x - a ) ^ ( n + 1 ) )
                  )
                  /
                  ( ! ` ( n + 1 ) )
                )
            ) $.
$}

${
  $d a c f n x $.

  thousand-theorems-metamath-Q1137206-taylor-mean-remainder-cauchy $a |-
    A. a e. RR
      A. x e. RR
        A. n e. NN0
          A. f e. ( RR ^m RR )
            (
              (
                a < x
                /\
                ( Q1137206Smooth f a x n )
              )
              ->
              E. c e. ( Q1137206Ioo a x )
                (
                  ( f ` x )
                  -
                  ( Q1137206Taylor f a x n )
                )
                =
                (
                  (
                    (
                      (
                        ( Q1137206Iter f a x ( n + 1 ) )
                        ` c
                      )
                      x.
                      ( ( x - c ) ^ n )
                    )
                    /
                    ( ! ` n )
                  )
                  x.
                  ( x - a )
                )
            ) $.
$}
