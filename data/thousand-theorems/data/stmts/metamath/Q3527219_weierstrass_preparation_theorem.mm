$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527219
  (thousand-theorems__metamath__Q3527219), "Weierstrass preparation theorem":
  over a commutative local ring complete in its maximal-ideal adic topology,
  every power series nonzero modulo the maximal ideal factors as a
  distinguished polynomial times a unit power series. This file contains no
  proof.

  SetMM's Poly1 ` R is the finite-support univariate polynomial ring and
  PwSer1 ` R is the univariate formal-power-series ring over R; Poly1 ` R is
  represented as a subring of PwSer1 ` R. Q3527219MaximalIdeal R is the
  unique maximal ideal of the local ring R.

  Q3527219IdealPower uses multiplication in SetMM's semiring of ideals.
  Q3527219AdicComplete is exactly Mathlib's IsAdicComplete predicate:
  separatedness for all powers of the ideal together with convergence of
  every adic Cauchy sequence. Q3527219Distinguished says that the polynomial
  is monic and every coefficient below its degree lies in the maximal ideal.
  Nonvanishing after coefficientwise reduction to the residue field is
  expressed equivalently by the existence of a coefficient outside that
  ideal. Every declaration below is an unproved $a statement encoding; this
  database contains no $p proof.
$)

$[ lib/set.mm $]

$c Q3527219MaximalIdeal Q3527219IdealPower
   Q3527219AdicComplete Q3527219Distinguished $.

q3527219-maximal-ideal-syntax
  $a class ( Q3527219MaximalIdeal R ) $.
q3527219-ideal-power-syntax
  $a class ( Q3527219IdealPower R M n ) $.
q3527219-adic-complete-syntax
  $a wff ( Q3527219AdicComplete R M ) $.
q3527219-distinguished-syntax
  $a wff ( Q3527219Distinguished R M f ) $.

${
  q3527219-maximal-ideal-definition $a |- (
    Q3527219MaximalIdeal R
  ) = U. ( MaxIdeal ` R ) $.
$}

${
  $d M R n $.

  q3527219-ideal-power-definition $a |- (
    Q3527219IdealPower R M n
  ) = (
    n
    ( .g ` ( mulGrp ` ( IDLsrg ` R ) ) )
    M
  ) $.
$}

${
  $d L M R m n s x $.

  q3527219-adic-complete-definition $a |- (
    Q3527219AdicComplete R M
  ) <->
  (
    A. x e. ( Base ` R )
      (
        A. n e. NN0
          x e. ( Q3527219IdealPower R M n )
        ->
        x = ( 0g ` R )
      )
    /\
    A. s e. ( ( Base ` R ) ^m NN0 )
      (
        A. m e. NN0
          A. n e. NN0
            (
              m <_ n
              ->
              (
                ( s ` m )
                ( +g ` R )
                ( ( -g ` R ) ` ( s ` n ) )
              )
              e. ( Q3527219IdealPower R M m )
            )
        ->
        E. L e. ( Base ` R )
          A. n e. NN0
            (
              ( s ` n )
              ( +g ` R )
              ( ( -g ` R ) ` L )
            )
            e. ( Q3527219IdealPower R M n )
      )
  ) $.
$}

${
  $d M R d f i $.

  q3527219-distinguished-definition $a |- (
    Q3527219Distinguished R M f
  ) <->
  E. d e. NN0
    (
      ( ( coe1 ` f ) ` d ) = ( 1r ` R )
      /\
      A. i e. NN0
        (
          (
            i < d
            ->
            ( ( coe1 ` f ) ` i ) e. M
          )
          /\
          (
            d < i
            ->
            ( ( coe1 ` f ) ` i ) = ( 0g ` R )
          )
        )
    ) $.
$}

${
  $d R f g h n $.

  thousand-theorems-q3527219-weierstrass-preparation-theorem $a |-
    A. R e. ( CRing i^i LRing )
      (
        ( Q3527219AdicComplete R ( Q3527219MaximalIdeal R ) )
        ->
        A. g e. ( Base ` ( PwSer1 ` R ) )
          (
            E. n e. NN0
              -. ( ( coe1 ` g ) ` n )
                 e. ( Q3527219MaximalIdeal R )
            ->
            E. f e. ( Base ` ( Poly1 ` R ) )
              E. h e. ( Base ` ( PwSer1 ` R ) )
                (
                  ( Q3527219Distinguished
                    R ( Q3527219MaximalIdeal R ) f )
                  /\
                  h e. ( Unit ` ( PwSer1 ` R ) )
                  /\
                  g =
                    (
                      f
                      ( .r ` ( PwSer1 ` R ) )
                      h
                    )
                )
          )
      ) $.
$}
