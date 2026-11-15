$(
  Statement-only formalization of Thousand Theorems corpus artifact Q4830725
  (thousand-theorems__metamath__Q4830725), "Ax-Grothendieck theorem":
  over an algebraically closed field with finitely many coordinates, an
  injective polynomial self-map of an affine zero locus is surjective on that
  zero locus. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's S mPoly K is the full finite-support multivariate polynomial ring
  over K with arbitrary variable carrier S. QAGAlgClosed is the standard
  nonconstant-polynomial root property. QAGZeroLocus is exactly the set of
  K-valued assignments on which every polynomial in the ideal I vanishes.

  A tuple P in Base(S mPoly K) ^m S defines the polynomial map whose i-th
  coordinate at x is the SetMM evaluation of P(i) at x. The final assertion
  states, with the source implication scopes, that if this map preserves the
  zero locus and is injective there, then it is surjective there. Every
  declaration below is an unproved $a statement encoding; there are no $p
  proof statements.
$)

$c QAGAlgClosed QAGZeroLocus $.

qag-algebraically-closed-syntax $a wff ( QAGAlgClosed K ) $.
qag-zero-locus-syntax $a class ( QAGZeroLocus K S I ) $.

${
  $d K c p x $.

  qag-algebraically-closed-definition $a |- (
    ( QAGAlgClosed K )
    <->
    (
      K e. Field
      /\
      A. p e. ( Base ` ( 1o mPoly K ) )
        (
          A. c e. ( Base ` K )
            p =/= ( ( algSc ` ( 1o mPoly K ) ) ` c )
          ->
          E. x e. ( Base ` K )
            ( ( ( eval1 ` K ) ` p ) ` x ) = ( 0g ` K )
        )
    )
  ) $.
$}

${
  $d I K S p x $.

  qag-zero-locus-definition $a |- (
    QAGZeroLocus K S I
  ) = {
    x e. ( ( Base ` K ) ^m S ) |
    A. p e. I
      ( ( ( S eval K ) ` p ) ` x ) = ( 0g ` K )
  } $.
$}

${
  $d I K P S i x y $.

  thousand-theorems-q4830725-ax-grothendieck-zero-locus $a |-
    A. K e. Field
      A. S e. Fin
        A. I e. ( LIdeal ` ( S mPoly K ) )
          A. P e. ( ( Base ` ( S mPoly K ) ) ^m S )
            (
              ( QAGAlgClosed K )
              ->
              (
                A. x e. ( QAGZeroLocus K S I )
                  (
                    i e. S |->
                      ( ( ( S eval K ) ` ( P ` i ) ) ` x )
                  ) e. ( QAGZeroLocus K S I )
                ->
                (
                  A. x e. ( QAGZeroLocus K S I )
                    A. y e. ( QAGZeroLocus K S I )
                      (
                        (
                          i e. S |->
                            ( ( ( S eval K ) ` ( P ` i ) ) ` x )
                        )
                        =
                        (
                          i e. S |->
                            ( ( ( S eval K ) ` ( P ` i ) ) ` y )
                        )
                        ->
                        x = y
                      )
                  ->
                  A. y e. ( QAGZeroLocus K S I )
                    E. x e. ( QAGZeroLocus K S I )
                      (
                        i e. S |->
                          ( ( ( S eval K ) ` ( P ` i ) ) ` x )
                      ) = y
                )
              )
            )
  $.
$}
