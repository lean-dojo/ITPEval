$(
  Statement-only formalization of Thousand Theorems corpus artifact Q978688
  (thousand-theorems__metamath__Q978688), "Gershgorin circle theorem": every
  eigenvalue of a square matrix over an arbitrary normed field lies in a
  closed Gershgorin ball determined by one row. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  K ranges over SetMM normed fields, I over arbitrary finite index carriers,
  and A over the full square-matrix space Base ` ( I Mat K ). The antecedent
  keeps the eigenvector witness internal: v is a coordinate vector with a
  nonzero entry and satisfies A v = u v pointwise.

  The conclusion is the closed-ball inequality
  norm(A(k,k) - u) <= sum_{j in I \ {k}} norm(A(k,j)). Reversing the
  subtraction inside the norm gives the source's distance from u to A(k,k).
  The following $a is the single unproved corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d A I K i j k r u v $.

  thousand-theorems-q978688-gershgorin-circle-theorem $a |-
    A. K e. ( NrmRing i^i Field )
      A. I e. Fin
        A. A e. ( Base ` ( I Mat K ) )
          A. u e. ( Base ` K )
            (
              (
                E. v e. ( ( Base ` K ) ^m I )
                  (
                    E. r e. I
                      ( v ` r ) =/= ( 0g ` K )
                    /\
                    A. i e. I
                      (
                        K gsum
                          (
                            j e. I |->
                              (
                                ( i A j )
                                ( .r ` K )
                                ( v ` j )
                              )
                          )
                      )
                      =
                      (
                        u
                        ( .r ` K )
                        ( v ` i )
                      )
                  )
              )
              ->
              E. k e. I
                (
                  (
                    ( norm ` K )
                    `
                    (
                      ( k A k )
                      ( +g ` K )
                      ( ( -g ` K ) ` u )
                    )
                  )
                  <_
                  (
                    sum_ j e. ( I \ { k } )
                      ( ( norm ` K ) ` ( k A j ) )
                  )
                )
            )
  $.
$}
