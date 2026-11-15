$(
  Statement-only formalization of Thousand Theorems corpus artifact Q720469
  (thousand-theorems__metamath__Q720469), catalog title
  "Chevalley-Warning theorem": over a finite field, if the sum of the total
  degrees of a finite selected family of multivariate polynomials is smaller
  than the number of variables, then the field characteristic divides the
  number of their common zeros. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite set S is a set-theoretic carrier for the source's arbitrary
  finite variable type. The arbitrary set J is the polynomial-family index
  type, and T is its selected finite subset. SetMM's S mPoly K and S eval K
  are the finite-support multivariate polynomial ring and its evaluation map.

  SetMM's mDeg assigns -oo to the zero polynomial, whereas Lean's totalDegree
  assigns zero. Q720469TotalDegree makes exactly that definitional adjustment.
  Every $a declaration below is an unproved statement encoding. This root file
  itself contains no $p proof declaration; proofs verified during ITPEval come
  only from the imported lib/set.mm library.
$)

$c Q720469TotalDegree $.

q720469-total-degree-syntax $a
  class ( Q720469TotalDegree K S P )
$.

${
  $d K P S $.

  $( Lean's totalDegree is zero on the zero polynomial, while SetMM's mDeg
     uses the extended value -oo there. $)
  q720469-total-degree-definition $a
    |- ( Q720469TotalDegree K S P )
       =
       if ( P = ( 0g ` ( S mPoly K ) ) ,
            0 ,
            ( ( S mDeg K ) ` P ) )
  $.
$}

${
  $d J K P S T f i p x $.

  thousand-theorems-metamath-Q720469 $a
    |-
    A. K e. Field
      ( ( Base ` K ) e. Fin
        ->
        A. S e. Fin
          A. J e. _V
            A. p e. NN0
              ( ( chr ` K ) = p
                ->
                A. T e. ( ~P J i^i Fin )
                  A. f
                    ( f : J --> ( Base ` ( S mPoly K ) )
                      ->
                      ( ( sum_ i e. T
                            ( Q720469TotalDegree K S ( f ` i ) ) )
                        < ( # ` S )
                        ->
                        p ||
                        ( # `
                          { x e. ( ( Base ` K ) ^m S ) |
                            A. i e. T
                              ( ( ( S eval K ) ` ( f ` i ) ) ` x )
                              =
                              ( 0g ` K ) } ) ) ) ) ) ) )
  $.
$}
