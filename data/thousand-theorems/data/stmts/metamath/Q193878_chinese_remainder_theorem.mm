$(
  Statement-only formalization of Thousand Theorems corpus artifact Q193878
  (thousand-theorems__metamath__Q193878), "Chinese remainder theorem":
  for a finite family of pairwise coprime ideals in an arbitrary commutative
  ring, the canonical map from the quotient by their intersection to the
  product of the individual quotient rings is a ring isomorphism. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  K is the carrier of the arbitrary finite index type, and F is the
  corresponding family of left ideals of the commutative ring R. Pairwise
  coprimality is expressed by the sum of each pair of distinct ideals being
  the whole ring carrier.

  The class abstraction in the left quotient is the bounded intersection of
  the ideals. Bounding it by Base ` R is essential for the empty family, when
  the intersection is the top ideal. The structure product Xs_ on the right
  is the dependent product of the individual quotient rings. The quantified
  RingIso witness sends the class of each x modulo the intersection to the
  function whose i-th value is the class of x modulo F ` i. Thus the final
  assertion renders the canonical equivalence
  Ideal.quotientInfRingEquivPiQuotient without supplying a proof.
$)

${
  $d E F K R i j x $.

  thousand-theorems-q193878-chinese-remainder-theorem $a |- (
    A. R e. CRing A. K e. Fin A. F
      (
        (
          F e. ( K --> ( LIdeal ` R ) )
          /\
          A. i e. K A. j e. ( K \ { i } )
            (
              ( F ` i )
              ( LSSum ` R )
              ( F ` j )
            ) = ( Base ` R )
        )
        ->
        E. E e.
          (
            (
              R /s
              (
                R ~QG
                { x e. ( Base ` R ) |
                  A. i e. K x e. ( F ` i )
                }
              )
            )
            RingIso
            (
              R Xs_
              (
                i e. K |->
                  (
                    R /s
                    ( R ~QG ( F ` i ) )
                  )
              )
            )
          )
          A. x e. ( Base ` R )
            (
              E
              `
              [ x ]
              (
                R ~QG
                { x e. ( Base ` R ) |
                  A. i e. K x e. ( F ` i )
                }
              )
            )
            =
            (
              i e. K |->
                [ x ] ( R ~QG ( F ` i ) )
            )
      )
  ) $.
$}
