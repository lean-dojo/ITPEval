$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binary_sqrt_BinarySqrt_sqrtqtvc: the binary-square-root step
  verification condition preserves the square-bracketing invariant while
  doubling the integer scale or selecting the next real approximation.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's RR and ZZ are the full real-number and integer domains. The source
  Boolean is represented exactly by the two-element carrier 2, with true=1
  and false=0. NTP4VCSqrtCeil is definitionally equal to
  ceil(max(r,1)/eps); its conditional is the real maximum in a linear order.

  The source let-bound integer and real values are substituted by 2*n and
  2*(n*eps). Proposition-valued conditionals are rendered as exhaustive
  guarded disjunctions, while the term-valued conditional selecting the next
  result uses SetMM's class conditional. These encodings are bidirectionally
  equivalent to the source conditionals. Splitting the typed parameters and
  assumptions into scoped essential hypotheses is equivalent to the source
  theorem context, and the result and approximation witnesses retain their
  full real quantifier domains. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

$c NTP4VCSqrtCeil $.

ntp4vc-sqrt-ceil-syntax $a class ( NTP4VCSqrtCeil A B ) $.

ntp4vc-sqrt-ceil-definition $a |- (
  NTP4VCSqrtCeil A B
) = (
  |^ ` (
    if ( A < 1 , 1 , A )
    /
    B
  )
) $.

${
  $d x y A B C D $.

  $( Source parameters: A=r, B=eps0, C=n, and D=o1. $)

  ntp4vc-r-real $e |- A e. RR $.
  ntp4vc-eps-real $e |- B e. RR $.
  ntp4vc-n-integer $e |- C e. ZZ $.
  ntp4vc-o1-boolean $e |- D e. 2 $.

  ntp4vc-r-nonnegative $e |- 0 <_ A $.
  ntp4vc-eps-positive $e |- 0 < B $.
  ntp4vc-n-positive $e |- 1 <_ C $.
  ntp4vc-o1-definition $e |- D = if (
    A < ( C x. B ) ,
    if ( 1 < ( C x. B ) , 1 , 0 ) ,
    0
  ) $.

  ntp4vc-pearl-binary-sqrt-vc $a |- (
    (
      D =/= 1
      ->
      (
        (
          0 <_ ( ( NTP4VCSqrtCeil A B ) - C )
          /\
          (
            ( NTP4VCSqrtCeil A B ) - ( 2 x. C )
          )
          <
          (
            ( NTP4VCSqrtCeil A B ) - C
          )
        )
        /\
        (
          0 <_ A
          /\
          (
            (
              0 < B
              /\
              1 <_ ( 2 x. C )
            )
            /\
            (
              2 x. ( C x. B )
            )
            =
            (
              ( 2 x. C ) x. B
            )
          )
        )
      )
    )
    /\
    A. x e. RR
      (
        (
          (
            D = 1
            /\
            x = 0
          )
          \/
          (
            D =/= 1
            /\
            E. y e. RR
              (
                (
                  (
                    ( y x. y ) <_ A
                    /\
                    A
                    <
                    (
                      ( y + ( 2 x. ( C x. B ) ) )
                      x.
                      ( y + ( 2 x. ( C x. B ) ) )
                    )
                  )
                  /\
                  x = if (
                    (
                      ( y + ( C x. B ) )
                      x.
                      ( y + ( C x. B ) )
                    )
                    <_
                    A ,
                    ( y + ( C x. B ) ) ,
                    y
                  )
                )
              )
          )
        )
        ->
        (
          ( x x. x ) <_ A
          /\
          A
          <
          (
            ( x + ( C x. B ) )
            x.
            ( x + ( C x. B ) )
          )
        )
      )
  ) $.
$}
