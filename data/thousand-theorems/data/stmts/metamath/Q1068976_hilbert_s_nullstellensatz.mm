$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1068976
  (thousand-theorems__metamath__Q1068976), "Hilbert's Nullstellensatz":
  over an algebraically closed field extension, the ideal of multivariate
  polynomials vanishing on the zero locus of an arbitrary ideal equals that
  ideal's radical. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's S mPoly F is the multivariate polynomial ring over the field F
  with arbitrary variable carrier S. QNSAlgClosed is the usual nonconstant
  polynomial root property. QNSRadical uses positive powers in the
  multiplicative monoid of S mPoly F.

  For a field homomorphism A : F -> K, composition A o. p maps the
  coefficients of p into K. The standard SetMM evaluation map then evaluates
  that polynomial at an arbitrary assignment S -> Base(K). Thus
  QNSZeroLocus and QNSVanishingIdeal are exactly the K-valued zero locus and
  its ideal of F-coefficient polynomials. Every declaration below is an
  unproved $a statement encoding; this database contains no $p proof.
$)

$c QNSAlgClosed QNSRadical QNSZeroLocus QNSVanishingIdeal $.

qns-algebraically-closed-syntax $a wff ( QNSAlgClosed K ) $.
qns-radical-syntax $a class ( QNSRadical F S I ) $.
qns-zero-locus-syntax $a class ( QNSZeroLocus F K A S I ) $.
qns-vanishing-ideal-syntax $a class ( QNSVanishingIdeal F K A S Z ) $.

${
  $d K c p x $.

  qns-algebraically-closed-definition $a |- (
    ( QNSAlgClosed K )
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
  $d F I S n p $.

  qns-radical-definition $a |- (
    QNSRadical F S I
  ) = {
    p e. ( Base ` ( S mPoly F ) ) |
    E. n e. NN
      ( n ( .g ` ( mulGrp ` ( S mPoly F ) ) ) p ) e. I
  } $.
$}

${
  $d A F I K S p x $.

  qns-zero-locus-definition $a |- (
    QNSZeroLocus F K A S I
  ) = {
    x e. ( ( Base ` K ) ^m S ) |
    A. p e. I
      ( ( ( S eval K ) ` ( A o. p ) ) ` x ) = ( 0g ` K )
  } $.
$}

${
  $d A F K S Z p x $.

  qns-vanishing-ideal-definition $a |- (
    QNSVanishingIdeal F K A S Z
  ) = {
    p e. ( Base ` ( S mPoly F ) ) |
    A. x e. Z
      ( ( ( S eval K ) ` ( A o. p ) ) ` x ) = ( 0g ` K )
  } $.
$}

${
  $d A F I K S $.

  thousand-theorems-q1068976-hilbert-nullstellensatz $a |-
    A. F e. Field
      A. K e. Field
        A. A e. ( F RingHom K )
          A. S e. Fin
            A. I e. ( LIdeal ` ( S mPoly F ) )
              (
                ( QNSAlgClosed K )
                ->
                (
                  QNSVanishingIdeal F K A S
                    ( QNSZeroLocus F K A S I )
                )
                =
                ( QNSRadical F S I )
              )
  $.
$}
