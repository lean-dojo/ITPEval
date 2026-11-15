$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2226625
  (thousand-theorems__metamath__Q2226625), "Commandino's theorem": for a
  positive-dimensional simplex over a characteristic-zero division ring, the
  vector from a vertex to the simplex centroid is the dimension scalar times
  the vector from the centroid to the opposite-face centroid. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  K is an arbitrary division ring of characteristic zero, V is an arbitrary
  left K-module, n is a positive natural number, and F lists n+1 affinely
  independent vertices. Q2226625NatCast is the repeated-addition embedding of
  natural numbers into K. Q2226625AffineIndependent uses the finite-relation
  characterization: coefficients summing to zero and having zero weighted
  vector sum must all vanish.

  Choosing any affine origin identifies the source affine torsor with Base ` V
  while preserving point differences, affine independence, and centroids.
  Conversely, Base ` V is itself an affine torsor. Q2226625Centroid is the
  equal-weight average of all n+1 vertices, and
  Q2226625FaceOppositeCentroid is the equal-weight average of the n vertices
  other than i.

  The final declaration is the single unproved corpus $a statement. Every
  preceding $a declaration is syntax or a faithful definition, and this
  database contains no $p proof statement.
$)

$c
  Q2226625NatCast Q2226625CharZero Q2226625AffineIndependent
  Q2226625Centroid Q2226625FaceOppositeCentroid
$.

q2226625-natural-cast-syntax
  $a class ( Q2226625NatCast K N ) $.
q2226625-characteristic-zero-syntax
  $a wff ( Q2226625CharZero K ) $.
q2226625-affine-independent-syntax
  $a wff ( Q2226625AffineIndependent K V I F ) $.
q2226625-centroid-syntax
  $a class ( Q2226625Centroid K V N F ) $.
q2226625-face-opposite-centroid-syntax
  $a class ( Q2226625FaceOppositeCentroid K V N F I ) $.

q2226625-natural-cast-definition $a |-
  ( Q2226625NatCast K N )
  =
  ( N ( .g ` K ) ( 1r ` K ) )
$.

${
  $d K m $.

  q2226625-characteristic-zero-definition $a |- (
    ( Q2226625CharZero K )
    <->
    A. m e. NN
      ( Q2226625NatCast K m ) =/= ( 0g ` K )
  ) $.
$}

${
  $d F I K V c j $.

  q2226625-affine-independent-definition $a |- (
    ( Q2226625AffineIndependent K V I F )
    <->
    A. c e. ( ( Base ` K ) ^m I )
      (
        (
          (
            K gsum
              ( j e. I |-> ( c ` j ) )
          )
          =
          ( 0g ` K )
          /\
          (
            V gsum
              (
                j e. I |->
                  (
                    ( c ` j )
                    ( .s ` V )
                    ( F ` j )
                  )
              )
          )
          =
          ( 0g ` V )
        )
        ->
        A. j e. I
          ( c ` j ) = ( 0g ` K )
      )
  ) $.
$}

${
  $d F K N V j $.

  q2226625-centroid-definition $a |-
    ( Q2226625Centroid K V N F )
    =
    (
      (
        ( 1r ` K )
        ( /r ` K )
        ( Q2226625NatCast K ( N + 1 ) )
      )
      ( .s ` V )
      (
        V gsum
          (
            j e. ( 0 ..^ ( N + 1 ) ) |->
              ( F ` j )
          )
      )
    )
  $.
$}

${
  $d F I K N V j $.

  q2226625-face-opposite-centroid-definition $a |-
    ( Q2226625FaceOppositeCentroid K V N F I )
    =
    (
      (
        ( 1r ` K )
        ( /r ` K )
        ( Q2226625NatCast K N )
      )
      ( .s ` V )
      (
        V gsum
          (
            j e. ( ( 0 ..^ ( N + 1 ) ) \ { I } ) |->
              ( F ` j )
          )
      )
    )
  $.
$}

${
  $d F K V i j n $.

  thousand-theorems-q2226625-commandino-s-theorem $a |-
    A. K e. DivRing
      A. V e. { v e. LMod | ( Scalar ` v ) = K }
        A. n e. NN
          A. F e.
            (
              ( Base ` V )
              ^m
              ( 0 ..^ ( n + 1 ) )
            )
            (
              (
                ( Q2226625CharZero K )
                /\
                (
                  Q2226625AffineIndependent
                  K
                  V
                  ( 0 ..^ ( n + 1 ) )
                  F
                )
              )
              ->
              A. i e. ( 0 ..^ ( n + 1 ) )
                (
                  (
                    ( F ` i )
                    ( +g ` V )
                    (
                      ( -g ` V )
                      `
                      ( Q2226625Centroid K V n F )
                    )
                  )
                  =
                  (
                    ( Q2226625NatCast K n )
                    ( .s ` V )
                    (
                      ( Q2226625Centroid K V n F )
                      ( +g ` V )
                      (
                        ( -g ` V )
                        `
                        (
                          Q2226625FaceOppositeCentroid
                          K
                          V
                          n
                          F
                          i
                        )
                      )
                    )
                  )
                )
            )
  $.
$}
