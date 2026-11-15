$(
  Statement-only formalization of Thousand Theorems corpus artifact Q776578
  (thousand-theorems__metamath__Q776578), "Artin-Wedderburn theorem":
  every semisimple ring carrying an algebra structure over an arbitrary
  commutative semiring is algebra-equivalent to a finite product of nonzero
  square matrix rings over division algebras. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q776578AlgebraMap K R A says that A is the central unital semiring
  homomorphism from the commutative semiring K to the ring R that specifies a
  K-algebra structure.

  Q776578Semisimple R says that every left ideal of R has a complementary left
  ideal: their intersection is the zero ideal and every ring element is a sum
  of one element from each ideal. Over ZFC this is bidirectionally equivalent
  to semisimplicity of the left regular module, which is Mathlib's
  IsSemisimpleRing condition.

  Q776578Target K n D d is the dependent product, indexed by 0 ..^ n, of the
  d(i)-by-d(i) matrix rings over D(i). The scalar slot K records the common
  base semiring; the final assertion explicitly specifies its induced central
  scalar map entry by entry.

  The final declaration is the single unproved $a corpus statement. All
  preceding $a declarations are syntax or faithful bidirectional definitions,
  and this root statement file contains no $p proof statement.
$)

$c Q776578AlgebraMap Q776578Semisimple Q776578Target $.

q776578-algebra-map-syntax $a
  wff ( Q776578AlgebraMap K R A ) $.

q776578-semisimple-syntax $a
  wff ( Q776578Semisimple R ) $.

q776578-target-syntax $a
  class ( Q776578Target K n D d ) $.

${
  $d A K R a b x $.

  q776578-algebra-map-definition $a |-
    ( Q776578AlgebraMap K R A )
    <->
    (
      ( K e. CSRing /\ R e. Ring )
      /\
      (
        A : ( Base ` K ) --> ( Base ` R )
        /\
        (
          (
            ( A ` ( 0g ` K ) ) = ( 0g ` R )
            /\
            ( A ` ( 1r ` K ) ) = ( 1r ` R )
          )
          /\
          (
            A. a e. ( Base ` K ) A. b e. ( Base ` K )
              (
                (
                  A ` ( a ( +g ` K ) b )
                )
                =
                (
                  ( A ` a ) ( +g ` R ) ( A ` b )
                )
                /\
                (
                  A ` ( a ( .r ` K ) b )
                )
                =
                (
                  ( A ` a ) ( .r ` R ) ( A ` b )
                )
              )
            /\
            A. a e. ( Base ` K ) A. x e. ( Base ` R )
              (
                ( A ` a ) ( .r ` R ) x
              )
              =
              (
                x ( .r ` R ) ( A ` a )
              )
          )
        )
      )
    )
  $.
$}

${
  $d I J R x y z $.

  q776578-semisimple-definition $a |-
    ( Q776578Semisimple R )
    <->
    (
      R e. Ring
      /\
      A. I e. ( LIdeal ` R )
        E. J e. ( LIdeal ` R )
          (
            ( I i^i J ) = { ( 0g ` R ) }
            /\
            A. x e. ( Base ` R )
              E. y e. I E. z e. J
                x = ( y ( +g ` R ) z )
          )
    )
  $.
$}

${
  $d D K d i n $.

  q776578-target-definition $a |-
    ( Q776578Target K n D d )
    =
    (
      K Xs_
      (
        i e. ( 0 ..^ n ) |->
          (
            ( 0 ..^ ( d ` i ) ) Mat ( D ` i )
          )
      )
    )
  $.
$}

${
  $d A B C D E K R a d i j k n $.

  thousand-theorems-q776578-artin-wedderburn-theorem $a |-
    A. K A. R A. A
      (
        (
          ( Q776578AlgebraMap K R A )
          /\
          ( Q776578Semisimple R )
        )
        ->
        E. n e. NN0 E. D E. d E. B E. C E. E
          (
            D : ( 0 ..^ n ) --> DivRing
            /\
            (
              d : ( 0 ..^ n ) --> NN
              /\
              (
                (
                  B Fn ( 0 ..^ n )
                  /\
                  A. i e. ( 0 ..^ n )
                    ( Q776578AlgebraMap K ( D ` i ) ( B ` i ) )
                )
                /\
                (
                  (
                    ( Q776578AlgebraMap
                      K
                      ( Q776578Target K n D d )
                      C )
                    /\
                    A. a e. ( Base ` K ) A. i e. ( 0 ..^ n )
                      A. j e. ( 0 ..^ ( d ` i ) )
                        A. k e. ( 0 ..^ ( d ` i ) )
                          (
                            j ( ( C ` a ) ` i ) k
                          )
                          =
                          if (
                            j = k
                            ,
                            ( ( B ` i ) ` a )
                            ,
                            ( 0g ` ( D ` i ) )
                          )
                  )
                  /\
                  (
                    E e. (
                      R RingIso ( Q776578Target K n D d )
                    )
                    /\
                    A. a e. ( Base ` K )
                      (
                        E ` ( A ` a )
                      )
                      =
                      ( C ` a )
                  )
                )
              )
            )
          )
      )
  $.
$}
