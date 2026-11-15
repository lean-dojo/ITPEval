$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2379132
  (thousand-theorems__metamath__Q2379132), "Going-up and going-down
  theorems". It states the two indexed going-up results, the prime-spectrum
  characterization of going-down, and the localized-spectrum surjectivity
  criterion. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q2379132MapPolynomial says that Q is obtained from P by applying the ring
  homomorphism A coefficientwise. Q2379132IntegralExtension says that every
  element of S is a root of such a transported monic polynomial over R. This
  is the usual elementwise definition of an integral R-algebra structure on S.

  Q2379132HasGoingDown is the prime-ideal lifting property: if p is contained
  in q and Q contracts to q, then some P contained in Q contracts to p.
  Q2379132GeneralizingPrimeSpectrumComap gives the equivalent pointwise
  generalizing-map condition. Q2379132LocalPrimeSpectrumComapSurjective is
  the same lifting condition at one fixed prime Q, corresponding to
  surjectivity after localization at Q and its contraction.

  Every declaration introduced below by this root artifact is an unproved $a
  statement encoding, and the root artifact adds no $p proof. The imported
  lib/set.mm supplies the library's existing proofs.
$)

$c Q2379132MapPolynomial Q2379132IntegralExtension
   Q2379132HasGoingDown Q2379132GeneralizingPrimeSpectrumComap
   Q2379132LocalPrimeSpectrumComapSurjective $.

q2379132-map-polynomial-syntax
  $a wff ( Q2379132MapPolynomial R S A P Q ) $.
q2379132-integral-extension-syntax
  $a wff ( Q2379132IntegralExtension R S A ) $.
q2379132-has-going-down-syntax
  $a wff ( Q2379132HasGoingDown R S A ) $.
q2379132-generalizing-prime-spectrum-comap-syntax
  $a wff ( Q2379132GeneralizingPrimeSpectrumComap R S A ) $.
q2379132-local-prime-spectrum-comap-surjective-syntax
  $a wff ( Q2379132LocalPrimeSpectrumComapSurjective R S A Q ) $.

${
  $d A P Q R S k $.

  q2379132-map-polynomial-definition $a |- (
    Q2379132MapPolynomial R S A P Q
  ) <->
  (
    P e. ( Base ` ( Poly1 ` R ) )
    /\
    (
      Q e. ( Base ` ( Poly1 ` S ) )
      /\
      A. k e. NN0
        (
          ( ( coe1 ` Q ) ` k )
          =
          ( A ` ( ( coe1 ` P ) ` k ) )
        )
    )
  ) $.
$}

${
  $d A R S p q x $.

  q2379132-integral-extension-definition $a |- (
    Q2379132IntegralExtension R S A
  ) <->
  (
    A. x e. ( Base ` S )
      E. p e. ( Monic1p ` R )
        E. q e. ( Base ` ( Poly1 ` S ) )
          (
            ( Q2379132MapPolynomial R S A p q )
            /\
            (
              ( ( ( eval1 ` S ) ` q ) ` x )
              =
              ( 0g ` S )
            )
          )
  ) $.
$}

${
  $d A R S i j p q $.

  q2379132-has-going-down-definition $a |- (
    Q2379132HasGoingDown R S A
  ) <->
  (
    A. p e. ( PrmIdeal ` R )
      A. q e. ( PrmIdeal ` R )
        A. i e. ( PrmIdeal ` S )
          (
            (
              p C_ q
              /\
              ( ( `' A " i ) = q )
            )
            ->
            E. j e. ( PrmIdeal ` S )
              (
                j C_ i
                /\
                ( ( `' A " j ) = p )
              )
          )
  ) $.
$}

${
  $d A R S i j p $.

  q2379132-generalizing-prime-spectrum-comap-definition $a |- (
    Q2379132GeneralizingPrimeSpectrumComap R S A
  ) <->
  (
    A. i e. ( PrmIdeal ` S )
      A. p e. ( PrmIdeal ` R )
        (
          p C_ ( `' A " i )
          ->
          E. j e. ( PrmIdeal ` S )
            (
              j C_ i
              /\
              ( ( `' A " j ) = p )
            )
        )
  ) $.
$}

${
  $d A Q R S j p $.

  q2379132-local-prime-spectrum-comap-surjective-definition $a |- (
    Q2379132LocalPrimeSpectrumComapSurjective R S A Q
  ) <->
  (
    A. p e. ( PrmIdeal ` R )
      (
        p C_ ( `' A " Q )
        ->
        E. j e. ( PrmIdeal ` S )
          (
            j C_ Q
            /\
            ( ( `' A " j ) = p )
          )
      )
  ) $.
$}

${
  $d a p q r s $.

  thousand-theorems-q2379132-going-up-and-going-down-theorems $a |-
    A. r e. CRing
      A. s e. IDomn
        A. a e. ( r RingHom s )
          A. p e. ( PrmIdeal ` r )
            (
              (
                ( Q2379132IntegralExtension r s a )
                /\
                ( ( `' a " { ( 0g ` s ) } ) C_ p )
              )
              ->
              E. q e. ( PrmIdeal ` s )
                ( ( `' a " q ) = p )
            )
  $.
$}

${
  $d a i p q r s $.

  thousand-theorems-q2379132-going-up-above-prime $a |-
    A. r e. CRing
      A. s e. CRing
        A. a e. ( r RingHom s )
          A. p e. ( PrmIdeal ` r )
            A. i e. ( PrmIdeal ` s )
              (
                (
                  ( Q2379132IntegralExtension r s a )
                  /\
                  ( ( `' a " i ) C_ p )
                )
                ->
                E. q e. ( PrmIdeal ` s )
                  (
                    i C_ q
                    /\
                    ( ( `' a " q ) = p )
                  )
              )
  $.
$}

${
  $d a r s $.

  thousand-theorems-q2379132-going-down-iff-generalizing $a |-
    A. r e. CRing
      A. s e. CRing
        A. a e. ( r RingHom s )
          (
            ( Q2379132HasGoingDown r s a )
            <->
            ( Q2379132GeneralizingPrimeSpectrumComap r s a )
          )
  $.
$}

${
  $d a i r s $.

  thousand-theorems-q2379132-going-down-from-local-surjectivity $a |-
    A. r e. CRing
      A. s e. CRing
        A. a e. ( r RingHom s )
          (
            (
              A. i e. ( PrmIdeal ` s )
                (
                  Q2379132LocalPrimeSpectrumComapSurjective
                    r s a i
                )
            )
            ->
            ( Q2379132HasGoingDown r s a )
          )
  $.
$}
