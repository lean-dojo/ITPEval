$(
  Statement-only formalization of "Taylor's Theorem" from Hundred Theorems
  item 035. It states the real Taylor formula with Lagrange remainder for a
  function on the unordered closed interval between two distinct real
  points, using relative iterated derivatives. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The repeated class

    { t e. RR |
      ( ( A <_ t /\ t <_ X ) \/ ( X <_ t /\ t <_ A ) ) }

  is the unordered closed interval with endpoints A and X. Replacing both
  non-strict inequalities by strict inequalities gives its open interior.

  The first smoothness premise says that the restriction of F to the closed
  interval is C^N there. The second says that its N-th relative derivative,
  restricted to the open interval, is differentiable at every point of that
  interval. The conclusion gives an internal witness c and expands the
  degree-N Taylor polynomial as the native finite sum from 0 through N.
$)

${
  $d c A $.
  $d c F $.
  $d c N $.
  $d c X $.
  $d c k $.
  $d c t $.
  $d k A $.
  $d k F $.
  $d k N $.
  $d k X $.
  $d k t $.
  $d t A $.
  $d t F $.
  $d t N $.
  $d t X $.

  taylor-theorem-with-lagrange-remainder $a |- (
    (
      (
        (
          ( A e. RR /\ X e. RR )
          /\
          ( N e. NN0 /\ A =/= X )
        )
        /\
        F : RR --> RR
      )
      /\
      (
        (
          F |`
            { t e. RR |
              ( ( A <_ t /\ t <_ X ) \/ ( X <_ t /\ t <_ A ) ) }
        )
        e.
        (
          (
            C^n `
              { t e. RR |
                ( ( A <_ t /\ t <_ X ) \/ ( X <_ t /\ t <_ A ) ) }
          )
          ` N
        )
        /\
        (
          { t e. RR |
            ( ( A < t /\ t < X ) \/ ( X < t /\ t < A ) ) }
          C_
          dom
            (
              { t e. RR |
                ( ( A < t /\ t < X ) \/ ( X < t /\ t < A ) ) }
              _D
              (
                (
                  (
                    { t e. RR |
                      ( ( A <_ t /\ t <_ X ) \/
                        ( X <_ t /\ t <_ A ) ) }
                    Dn
                    (
                      F |`
                        { t e. RR |
                          ( ( A <_ t /\ t <_ X ) \/
                            ( X <_ t /\ t <_ A ) ) }
                    )
                  )
                  ` N
                )
                |`
                { t e. RR |
                  ( ( A < t /\ t < X ) \/ ( X < t /\ t < A ) ) }
              )
            )
        )
      )
    )
    ->
    E. c e.
      { t e. RR |
        ( ( A < t /\ t < X ) \/ ( X < t /\ t < A ) ) }
      (
        (
          ( F ` X )
          -
          sum_ k e. ( 0 ... N )
            (
              (
                (
                  (
                    (
                      { t e. RR |
                        ( ( A <_ t /\ t <_ X ) \/
                          ( X <_ t /\ t <_ A ) ) }
                      Dn
                      (
                        F |`
                          { t e. RR |
                            ( ( A <_ t /\ t <_ X ) \/
                              ( X <_ t /\ t <_ A ) ) }
                      )
                    )
                    ` k
                  )
                  ` A
                )
                /
                ( ! ` k )
              )
              x.
              ( ( X - A ) ^ k )
            )
        )
        =
        (
          (
            (
              (
                (
                  { t e. RR |
                    ( ( A <_ t /\ t <_ X ) \/
                      ( X <_ t /\ t <_ A ) ) }
                  Dn
                  (
                    F |`
                      { t e. RR |
                        ( ( A <_ t /\ t <_ X ) \/
                          ( X <_ t /\ t <_ A ) ) }
                  )
                )
                ` ( N + 1 )
              )
              ` c
            )
            x.
            ( ( X - A ) ^ ( N + 1 ) )
          )
          /
          ( ! ` ( N + 1 ) )
        )
      )
  ) $.
$}
