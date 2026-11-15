$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1227702
  (thousand-theorems__metamath__Q1227702), "Dirichlet's unit theorem": for a
  number field, presented as an arbitrary finite-dimensional extension of the
  rational field, the units of its ring of integers modulo torsion have a
  Z-basis indexed by the number of infinite places minus one, and every unit
  has a unique expression as a torsion unit times integral powers of lifted
  basis units. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  K is an arbitrary field and A is its rational-field homomorphism.
  SetMM realizes the rational field as ( CCfld |`s QQ ).
  Q1227702ExtensionModule is K as a vector space over that field, with scalar
  action c . x = A(c) * x. Q1227702FiniteDimensional says that this vector
  space has a finite basis, exactly the number-field hypothesis in the Lean
  source. A rational-field homomorphism into a field is unique, so making A
  explicit does not restrict K to a chosen subfield of CCfld.

  Q1227702RingOfIntegers restricts K to the elements integral over the
  canonical image of Z. Q1227702UnitGroup is its multiplicative group of
  units, and Q1227702Torsion is the subgroup of units whose group-element
  order is a positive integer.

  Q1227702Embeddings is the set of field embeddings into the complex field.
  Q1227702InfinitePlaces is their orbit set under complex conjugation, written
  as the set of pairs { f, * o. f }. Its cardinal minus one is the source
  rank. The interval 1 ... rank is a harmless one-based reindexing of Lean's
  Fin rank.

  In the final assertion, ran B is a basis of the canonical Z-module attached
  to the unit quotient, F chooses unit representatives of its indexed basis,
  and z ranges over the product of the torsion subgroup with all
  integer-valued exponent functions. SetMM's gsum uses the group operation,
  so on this multiplicative unit group it is the finite product in the Lean
  statement. Every declaration is an unproved $a statement; there is no $p
  proof statement in this file.
$)

$c Q1227702ExtensionModule Q1227702FiniteDimensional
   Q1227702RingOfIntegers Q1227702UnitGroup Q1227702Torsion
   Q1227702Embeddings Q1227702InfinitePlaces Q1227702Rank $.

q1227702-extension-module-syntax $a class
  ( Q1227702ExtensionModule K A ) $.
q1227702-finite-dimensional-syntax $a wff
  ( Q1227702FiniteDimensional K A ) $.
q1227702-ring-of-integers-syntax $a class
  ( Q1227702RingOfIntegers K ) $.
q1227702-unit-group-syntax $a class
  ( Q1227702UnitGroup K ) $.
q1227702-torsion-syntax $a class
  ( Q1227702Torsion K ) $.
q1227702-embeddings-syntax $a class
  ( Q1227702Embeddings K ) $.
q1227702-infinite-places-syntax $a class
  ( Q1227702InfinitePlaces K ) $.
q1227702-rank-syntax $a class
  ( Q1227702Rank K ) $.

${
  $d A K a x $.

  q1227702-extension-module-definition $a |-
    ( Q1227702ExtensionModule K A )
    =
    (
      {
        <.
          ( Base ` ndx ) ,
          ( Base ` K )
        >. ,
        <.
          ( +g ` ndx ) ,
          ( +g ` K )
        >. ,
        <.
          ( Scalar ` ndx ) ,
          ( CCfld |`s QQ )
        >.
      }
      u.
      {
        <.
          ( .s ` ndx ) ,
          (
            a e. ( Base ` ( CCfld |`s QQ ) ) ,
            x e. ( Base ` K )
            |->
            ( ( A ` a ) ( .r ` K ) x )
          )
        >.
      }
    )
  $.
$}

${
  $d A K b $.

  q1227702-finite-dimensional-definition $a |- (
    Q1227702FiniteDimensional K A
  ) <->
  (
    E. b e.
      (
        LBasis `
        ( Q1227702ExtensionModule K A )
      )
      b e. Fin
  ) $.
$}

${
  q1227702-ring-of-integers-definition $a |-
    ( Q1227702RingOfIntegers K )
    =
    (
      K |`s
      ( K IntgRing ran ( ZRHom ` K ) )
    )
  $.
$}

${
  q1227702-unit-group-definition $a |-
    ( Q1227702UnitGroup K )
    =
    (
      ( mulGrp ` ( Q1227702RingOfIntegers K ) )
      |`s
      ( Unit ` ( Q1227702RingOfIntegers K ) )
    )
  $.
$}

${
  q1227702-torsion-definition $a |-
    ( Q1227702Torsion K )
    =
    (
      `' ( od ` ( Q1227702UnitGroup K ) ) " NN
    )
  $.
$}

${
  q1227702-embeddings-definition $a |-
    ( Q1227702Embeddings K )
    =
    ( K RingHom CCfld )
  $.
$}

${
  $d K f $.

  q1227702-infinite-places-definition $a |-
    ( Q1227702InfinitePlaces K )
    =
    ran
    (
      f e. ( Q1227702Embeddings K )
      |->
      { f , ( * o. f ) }
    )
  $.
$}

${
  q1227702-rank-definition $a |-
    ( Q1227702Rank K )
    =
    ( ( # ` ( Q1227702InfinitePlaces K ) ) - 1 )
  $.
$}

${
  $d A B F K i x z $.

  thousand-theorems-q1227702-dirichlet-unit-theorem $a |- (
    A. K e. Field
      A. A e. ( ( CCfld |`s QQ ) RingHom K )
        (
          ( Q1227702FiniteDimensional K A )
          ->
          E. B E. F
            (
              (
                B
                :
                ( 1 ... ( Q1227702Rank K ) )
                -1-1->
                (
                  Base `
                  (
                    ( Q1227702UnitGroup K )
                    /s
                    (
                      ( Q1227702UnitGroup K )
                      ~QG
                      ( Q1227702Torsion K )
                    )
                  )
                )
                /\
                ran B e.
                (
                  LBasis `
                  (
                    ZMod `
                    (
                      ( Q1227702UnitGroup K )
                      /s
                      (
                        ( Q1227702UnitGroup K )
                        ~QG
                        ( Q1227702Torsion K )
                      )
                    )
                  )
                )
              )
              /\
              (
                F
                :
                ( 1 ... ( Q1227702Rank K ) )
                -->
                ( Base ` ( Q1227702UnitGroup K ) )
                /\
                A. i e. ( 1 ... ( Q1227702Rank K ) )
                  [
                    ( F ` i )
                  ]
                  (
                    ( Q1227702UnitGroup K )
                    ~QG
                    ( Q1227702Torsion K )
                  )
                  =
                  ( B ` i )
              )
              /\
              A. x e. ( Base ` ( Q1227702UnitGroup K ) )
                E! z e.
                (
                  (
                    ( Q1227702Torsion K )
                    X.
                    (
                      ZZ
                      ^m
                      ( 1 ... ( Q1227702Rank K ) )
                    )
                  )
                  x
                  =
                  (
                    ( 1st ` z )
                    ( +g ` ( Q1227702UnitGroup K ) )
                    (
                      ( Q1227702UnitGroup K )
                      gsum
                      (
                        i e. ( 1 ... ( Q1227702Rank K ) )
                        |->
                        (
                          ( ( 2nd ` z ) ` i )
                          ( .g ` ( Q1227702UnitGroup K ) )
                          ( F ` i )
                        )
                      )
                    )
                  )
            )
        )
  ) $.
$}
