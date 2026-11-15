$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binomial_Top_computeqtvc: the binomial-coefficient computation
  verification condition initializes, advances, and returns the recurrence
  value up to the symmetric index min(k,n-k). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. A and B represent respectively the
  source infix_sl and comb constants as arbitrary total functions
  ZZ x ZZ -> ZZ. Their scoped essential hypotheses reproduce the complete
  source axioms: infix_sl is Euclidean integer division at every nonzero
  divisor, comb obeys Pascal's recurrence on 0 <= k <= n, and every such
  comb value is at least one. For a negative divisor, Euclidean division is
  the ceiling of the rational quotient; for a positive divisor, it is the
  floor.

  NTP4VCMin is the ordinary integer minimum, so substituting it for the
  source let-bound k1 is definitionally equivalent. Splitting the fixed
  constants, their axioms, the integer parameters, and the two theorem
  assumptions into scoped essential hypotheses is bidirectionally equivalent
  to the source context. Every i and r quantifier retains the full integer
  domain, and the conjunction and implication scopes follow the source
  statement exactly. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c NTP4VCMin $.

ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if (
  A <_ B ,
  A ,
  B
) $.

${
  $d i r x y A B C D $.

  $( A is the source infix_sl function and B is the source comb function. $)
  ntp4vc-infix-sl-function
    $e |- A e. ( ZZ ^m ( ZZ X. ZZ ) ) $.
  ntp4vc-comb-function
    $e |- B e. ( ZZ ^m ( ZZ X. ZZ ) ) $.

  ntp4vc-infix-sl-definition $e |- A. y e. ZZ A. x e. ZZ
    (
      y =/= 0
      ->
      (
        A ` <. x , y >.
      ) = if (
        0 < y ,
        ( |_ ` ( x / y ) ) ,
        ( |^ ` ( x / y ) )
      )
    ) $.

  ntp4vc-comb-definition $e |- A. x e. ZZ A. y e. ZZ
    (
      (
        0 <_ x
        /\
        x <_ y
      )
      ->
      (
        B ` <. y , x >.
      ) = if (
        (
          x = 0
          \/
          x = y
        ) ,
        1 ,
        (
          ( B ` <. ( y - 1 ) , x >. )
          +
          ( B ` <. ( y - 1 ) , ( x - 1 ) >. )
        )
      )
    ) $.

  ntp4vc-comb-positive $e |- A. x e. ZZ A. y e. ZZ
    (
      (
        0 <_ x
        /\
        x <_ y
      )
      ->
      1 <_ ( B ` <. y , x >. )
    ) $.

  $( Source theorem parameters: C=k and D=n. $)
  ntp4vc-k-integer $e |- C e. ZZ $.
  ntp4vc-n-integer $e |- D e. ZZ $.
  ntp4vc-k-nonnegative $e |- 0 <_ C $.
  ntp4vc-k-at-most-n $e |- C <_ D $.

  ntp4vc-pearl-binomial-compute-vc $a |- (
    (
      1
      <_
      (
        ( NTP4VCMin C ( D - C ) )
        +
        1
      )
      ->
      (
        (
          (
            1 <_ 1
            /\
            1
            <_
            (
              ( NTP4VCMin C ( D - C ) )
              +
              1
            )
          )
          /\
          1 = (
            B ` <. D , ( 1 - 1 ) >.
          )
        )
        /\
        A. r e. ZZ
          (
            A. i e. ZZ
              (
                (
                  (
                    (
                      1 <_ i
                      /\
                      i <_ ( NTP4VCMin C ( D - C ) )
                    )
                    /\
                    (
                      1 <_ i
                      /\
                      i
                      <_
                      (
                        ( NTP4VCMin C ( D - C ) )
                        +
                        1
                      )
                    )
                  )
                  /\
                  r = (
                    B ` <. D , ( i - 1 ) >.
                  )
                )
                ->
                (
                  i =/= 0
                  /\
                  (
                    (
                      1 <_ ( i + 1 )
                      /\
                      ( i + 1 )
                      <_
                      (
                        ( NTP4VCMin C ( D - C ) )
                        +
                        1
                      )
                    )
                    /\
                    (
                      A ` <.
                        (
                          r
                          x.
                          (
                            ( D - i )
                            +
                            1
                          )
                        ) ,
                        i
                      >.
                    ) = (
                      B ` <. D , ( ( i + 1 ) - 1 ) >.
                    )
                  )
                )
              )
            /\
            (
              (
                (
                  1
                  <_
                  (
                    ( NTP4VCMin C ( D - C ) )
                    +
                    1
                  )
                  /\
                  (
                    ( NTP4VCMin C ( D - C ) )
                    +
                    1
                  )
                  <_
                  (
                    ( NTP4VCMin C ( D - C ) )
                    +
                    1
                  )
                )
                /\
                r = (
                  B ` <.
                    D ,
                    (
                      (
                        ( NTP4VCMin C ( D - C ) )
                        +
                        1
                      )
                      -
                      1
                    )
                  >.
                )
              )
              ->
              r = ( B ` <. D , C >. )
            )
          )
      )
    )
    /\
    (
      (
        ( NTP4VCMin C ( D - C ) )
        +
        1
      )
      <
      1
      ->
      1 = ( B ` <. D , C >. )
    )
  ) $.
$}
