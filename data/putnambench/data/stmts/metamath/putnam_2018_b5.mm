$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_b5: a continuously differentiable map from the real plane
  to itself with positive partial derivatives and the stated differential
  inequality is injective. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P18B5D11, P18B5D12, P18B5D21, and P18B5D22 are the four coordinate
  partial derivatives of F. Their zero fallbacks make them total; the
  fallbacks are inactive under P18B5C1.

  P18B5C1 requires every coordinate slice derivative to exist and all four
  partial derivatives to be jointly continuous on RR X. RR. For a map
  between finite-dimensional real spaces, this is equivalent to continuous
  differentiability through order one.

  Ordered pairs identify RR X. RR with the source's two-dimensional real
  vectors. The positivity hypothesis covers all four partial derivatives,
  and the displayed inequality uses the two diagonal partials and the sum
  of the two cross-partials. The conclusion states injectivity directly.
  Every declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c P18B5D11 P18B5D12 P18B5D21 P18B5D22 P18B5C1 $.

p18b5-d11-syntax $a class ( P18B5D11 F x y ) $.
p18b5-d12-syntax $a class ( P18B5D12 F x y ) $.
p18b5-d21-syntax $a class ( P18B5D21 F x y ) $.
p18b5-d22-syntax $a class ( P18B5D22 F x y ) $.
p18b5-c1-syntax $a wff ( P18B5C1 F ) $.

${
  $d F t x y $.

  p18b5-d11-definition $a |- ( P18B5D11 F x y ) = if (
    x e.
      dom
        (
          RR _D
            (
              t e. RR |->
                ( 1st ` ( F ` <. t , y >. ) )
            )
        ) ,
    (
      (
        RR _D
          (
            t e. RR |->
              ( 1st ` ( F ` <. t , y >. ) )
          )
      )
      ` x
    ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p18b5-d12-definition $a |- ( P18B5D12 F x y ) = if (
    y e.
      dom
        (
          RR _D
            (
              t e. RR |->
                ( 1st ` ( F ` <. x , t >. ) )
            )
        ) ,
    (
      (
        RR _D
          (
            t e. RR |->
              ( 1st ` ( F ` <. x , t >. ) )
          )
      )
      ` y
    ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p18b5-d21-definition $a |- ( P18B5D21 F x y ) = if (
    x e.
      dom
        (
          RR _D
            (
              t e. RR |->
                ( 2nd ` ( F ` <. t , y >. ) )
            )
        ) ,
    (
      (
        RR _D
          (
            t e. RR |->
              ( 2nd ` ( F ` <. t , y >. ) )
          )
      )
      ` x
    ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p18b5-d22-definition $a |- ( P18B5D22 F x y ) = if (
    y e.
      dom
        (
          RR _D
            (
              t e. RR |->
                ( 2nd ` ( F ` <. x , t >. ) )
            )
        ) ,
    (
      (
        RR _D
          (
            t e. RR |->
              ( 2nd ` ( F ` <. x , t >. ) )
          )
      )
      ` y
    ) ,
    0
  ) $.
$}

${
  $d F d e t u v x y $.

  p18b5-c1-definition $a |- (
    ( P18B5C1 F )
    <->
    (
      F e. ( ( RR X. RR ) ^m ( RR X. RR ) )
      /\
      (
        A. x e. RR A. y e. RR
          (
            (
              x e.
                dom
                  (
                    RR _D
                      (
                        t e. RR |->
                          ( 1st ` ( F ` <. t , y >. ) )
                      )
                  )
              /\
              y e.
                dom
                  (
                    RR _D
                      (
                        t e. RR |->
                          ( 1st ` ( F ` <. x , t >. ) )
                      )
                  )
            )
            /\
            (
              x e.
                dom
                  (
                    RR _D
                      (
                        t e. RR |->
                          ( 2nd ` ( F ` <. t , y >. ) )
                      )
                  )
              /\
              y e.
                dom
                  (
                    RR _D
                      (
                        t e. RR |->
                          ( 2nd ` ( F ` <. x , t >. ) )
                      )
                  )
            )
          )
        /\
        A. x e. RR A. y e. RR A. e e. RR
          (
            0 < e
            ->
            E. d e. RR
              (
                0 < d
                /\
                A. u e. RR A. v e. RR
                  (
                    (
                      ( abs ` ( u - x ) ) < d
                      /\
                      ( abs ` ( v - y ) ) < d
                    )
                    ->
                    (
                      (
                        (
                          abs
                          `
                          (
                            ( P18B5D11 F u v )
                            -
                            ( P18B5D11 F x y )
                          )
                        )
                        < e
                        /\
                        (
                          abs
                          `
                          (
                            ( P18B5D12 F u v )
                            -
                            ( P18B5D12 F x y )
                          )
                        )
                        < e
                      )
                      /\
                      (
                        (
                          abs
                          `
                          (
                            ( P18B5D21 F u v )
                            -
                            ( P18B5D21 F x y )
                          )
                        )
                        < e
                        /\
                        (
                          abs
                          `
                          (
                            ( P18B5D22 F u v )
                            -
                            ( P18B5D22 F x y )
                          )
                        )
                        < e
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
  $d F p q x y $.

  putnambench-putnam-2018-b5 $a |-
    A. F e. ( ( RR X. RR ) ^m ( RR X. RR ) )
      (
        (
          (
            ( P18B5C1 F )
            /\
            A. x e. RR A. y e. RR
              (
                (
                  0 < ( P18B5D11 F x y )
                  /\
                  0 < ( P18B5D12 F x y )
                )
                /\
                (
                  0 < ( P18B5D21 F x y )
                  /\
                  0 < ( P18B5D22 F x y )
                )
              )
          )
          /\
          A. x e. RR A. y e. RR
            0
            <
            (
              (
                ( P18B5D11 F x y )
                x.
                ( P18B5D22 F x y )
              )
              -
              (
                ( 1 / 4 )
                x.
                (
                  (
                    ( P18B5D21 F x y )
                    +
                    ( P18B5D12 F x y )
                  )
                  ^ 2
                )
              )
            )
        )
        ->
        A. p e. ( RR X. RR ) A. q e. ( RR X. RR )
          (
            ( F ` p ) = ( F ` q )
            ->
            p = q
          )
      )
  $.
$}
