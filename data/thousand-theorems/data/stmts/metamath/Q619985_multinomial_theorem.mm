$(
  Statement-only formalization of Thousand Theorems corpus artifact Q619985
  (thousand-theorems__metamath__Q619985), "Multinomial theorem": in every
  semiring, the natural power of a finite sum of pairwise commuting values
  equals the multinomially weighted sum of their order-independent products.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q619985Anti A K n is the antidiagonal of exponent functions on the
  arbitrary ambient set A: its members are natural-valued total functions
  that vanish off K and whose values on K sum to n.

  Q619985Mult K n k is the multinomial coefficient, represented without
  division as the number of length-n words over K having multiplicity k(i)
  at each i in K.  For k in Q619985Anti A K n this is definitionally
  equivalent to n! / product_i k(i)!.

  The multiplicative gsum below is the order-independent finite product in
  the multiplicative monoid of R.  Its uniqueness is ensured by the stated
  pairwise commutation hypothesis, exactly as for Finset.noncommProd.
  The transparent definitions and the final $a assertion are unproved
  statement encodings; there is no $p proof in this file.
$)

$c Q619985Anti Q619985Mult $.

q619985-antidiag-syntax $a class ( Q619985Anti A K n ) $.
q619985-multinomial-syntax $a class ( Q619985Mult K n k ) $.

${
  $d A K i k n $.
  q619985-antidiag-definition $a
    |- ( Q619985Anti A K n ) =
      { k e. ( NN0 ^m A ) |
        ( A. i e. ( A \ K ) ( k ` i ) = 0
          /\
          ( sum_ i e. K ( k ` i ) ) = n ) } $.
$}

${
  $d K i j k n u $.
  q619985-multinomial-definition $a
    |- ( Q619985Mult K n k ) =
      ( # ` { u e. ( K ^m ( 1 ... n ) ) |
        A. i e. K
          ( # ` { j e. ( 1 ... n ) | ( u ` j ) = i } )
            = ( k ` i ) } ) $.
$}

${
  $d A K R f i j k n $.
  thousand-theorems-metamath-Q619985 $a
    |- A. R e. SRing
        A. A
          A. K e. Fin
            A. f e. ( ( Base ` R ) ^m A )
              A. n e. NN0
                ( ( K C_ A
                    /\
                    A. i e. K
                      A. j e. ( K \ { i } )
                        ( ( f ` i ) ( .r ` R ) ( f ` j ) )
                          =
                        ( ( f ` j ) ( .r ` R ) ( f ` i ) ) )
                  ->
                  ( n
                      ( .g ` ( mulGrp ` R ) )
                      ( R gsum ( i e. K |-> ( f ` i ) ) ) )
                    =
                  ( R gsum
                      ( k e. ( Q619985Anti A K n ) |->
                        ( ( ( Q619985Mult K n k )
                              ( .g ` R )
                              ( 1r ` R ) )
                            ( .r ` R )
                            ( ( mulGrp ` R ) gsum
                              ( i e. K |->
                                ( ( k ` i )
                                  ( .g ` ( mulGrp ` R ) )
                                  ( f ` i ) ) ) ) ) ) ) ) ) $.
$}
