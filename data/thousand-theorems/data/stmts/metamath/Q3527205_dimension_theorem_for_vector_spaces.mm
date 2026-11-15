$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527205
  (thousand-theorems__metamath__Q3527205), "Dimension theorem for vector
  spaces": any two indexed bases of an arbitrary semimodule over a semiring
  with invariant basis number have equipollent index sets. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's SLMod supplies arbitrary semimodules over arbitrary semirings.
  Q3527205FiniteSupport R I is the set of finitely supported coefficient
  functions from I to the carrier of R. Q3527205LinearEquiv R I J F says that
  F is a bijective additive and R-linear map between the corresponding free
  semimodules. Q3527205InvariantBasisNumber R is exactly the source property
  that linearly equivalent finite free R-semimodules have equal finite ranks.

  Q3527205IndexedBasis W I B says that B maps I into the carrier of W and that
  finite R-linear combination along B is a bijection onto W. This is the
  coefficient-map characterization of mathlib's Basis I R W. Equality of the
  lifted cardinals of I and J is rendered set-theoretically as equipollence
  I ~~ J.

  The final declaration is the single unproved $a corpus statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q3527205FiniteSupport Q3527205LinearEquiv Q3527205IndexedBasis
   Q3527205InvariantBasisNumber $.

q3527205-finite-support-syntax
  $a class ( Q3527205FiniteSupport R I ) $.

q3527205-linear-equiv-syntax
  $a wff ( Q3527205LinearEquiv R I J F ) $.

q3527205-indexed-basis-syntax
  $a wff ( Q3527205IndexedBasis W I B ) $.

q3527205-invariant-basis-number-syntax
  $a wff ( Q3527205InvariantBasisNumber R ) $.

${
  $d I R f $.

  q3527205-finite-support-definition $a |- (
    Q3527205FiniteSupport R I
  ) = {
    f e. ( ( Base ` R ) ^m I ) |
      f finSupp ( 0g ` R )
  } $.
$}

${
  $d F I J R a f g $.

  q3527205-linear-equiv-definition $a |- (
    ( Q3527205LinearEquiv R I J F )
    <->
    (
      F :
        ( Q3527205FiniteSupport R I )
        -1-1-onto->
        ( Q3527205FiniteSupport R J )
      /\
      (
        A. f e. ( Q3527205FiniteSupport R I )
          A. g e. ( Q3527205FiniteSupport R I )
            (
              F ` ( f oF ( +g ` R ) g )
            )
            =
            (
              ( F ` f ) oF ( +g ` R ) ( F ` g )
            )
        /\
        A. a e. ( Base ` R )
          A. f e. ( Q3527205FiniteSupport R I )
            (
              F `
              (
                ( I X. { a } ) oF ( .r ` R ) f
              )
            )
            =
            (
              ( J X. { a } ) oF ( .r ` R ) ( F ` f )
            )
      )
    )
  ) $.
$}

${
  $d B I W f $.

  q3527205-indexed-basis-definition $a |- (
    ( Q3527205IndexedBasis W I B )
    <->
    (
      B : I --> ( Base ` W )
      /\
      (
        f e. ( Q3527205FiniteSupport ( Scalar ` W ) I )
        |->
        (
          W gsum
          (
            f oF ( .s ` W ) B
          )
        )
      )
      :
      ( Q3527205FiniteSupport ( Scalar ` W ) I )
      -1-1-onto->
      ( Base ` W )
    )
  ) $.
$}

${
  $d F R m n $.

  q3527205-invariant-basis-number-definition $a |- (
    ( Q3527205InvariantBasisNumber R )
    <->
    (
      R e. SRing
      /\
      A. n e. NN0
        A. m e. NN0
          A. F
            (
              (
                Q3527205LinearEquiv
                R
                ( 0 ..^ n )
                ( 0 ..^ m )
                F
              )
              ->
              n = m
            )
    )
  ) $.
$}

${
  $d B C I J R W $.

  thousand-theorems-q3527205-dimension-theorem-for-vector-spaces $a |- (
    A. R A. W A. I A. J A. B A. C
      (
        (
          (
            ( Q3527205InvariantBasisNumber R )
            /\
            (
              W e. SLMod
              /\
              ( Scalar ` W ) = R
            )
          )
          /\
          (
            ( Q3527205IndexedBasis W I B )
            /\
            ( Q3527205IndexedBasis W J C )
          )
        )
        ->
        I ~~ J
      )
  ) $.
$}
