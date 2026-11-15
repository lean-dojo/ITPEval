$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527263
  (thousand-theorems__metamath__Q3527263), "Kleene fixed-point theorem": the
  least fixed point of an omega-Scott-continuous monotone self-map of an
  arbitrary complete lattice is the supremum of its finite iterates from
  bottom. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q3527263OmegaScottContinuous(K,F) packages the source type of F as an order
  endomorphism and says that F preserves the supremum of every increasing
  natural-number-indexed chain. Q3527263Lfp(K,F) is the infimum of the
  pre-fixed points of F. Q3527263Iterates(K,F) is the unique sequence starting
  at bottom and obtained by repeatedly applying F. Thus its range is exactly
  the family indexed in Lean by n |-> f^[n] bottom.

  The declarations before the final assertion are syntax or bidirectional
  definitions. The final $a assertion is the unproved corpus statement; this
  root artifact itself contains no $p statement.
$)

$c Q3527263OmegaScottContinuous Q3527263Lfp Q3527263Iterates $.

q3527263-osc-syntax $a wff
  ( Q3527263OmegaScottContinuous K F ) $.

q3527263-lfp-syntax $a class
  ( Q3527263Lfp K F ) $.

q3527263-iterates-syntax $a class
  ( Q3527263Iterates K F ) $.

$d C F K m n x y $.
q3527263-osc-definition $a |- ( ( Q3527263OmegaScottContinuous K F ) <->
  ( ( F : ( Base ` K ) --> ( Base ` K ) /\
      A. x e. ( Base ` K ) A. y e. ( Base ` K )
        ( x ( le ` K ) y ->
          ( F ` x ) ( le ` K ) ( F ` y ) ) ) /\
    A. C e. ( ( Base ` K ) ^m NN0 )
      ( A. m e. NN0 A. n e. NN0
          ( m <_ n -> ( C ` m ) ( le ` K ) ( C ` n ) ) ->
        ( F ` ( ( lub ` K ) ` ran C ) ) =
          ( ( lub ` K ) ` ( F " ran C ) ) ) ) ) $.

$d F K x $.
q3527263-lfp-definition $a |- ( ( Q3527263Lfp K F ) =
  ( ( glb ` K ) `
    { x e. ( Base ` K ) | ( F ` x ) ( le ` K ) x } ) ) $.

$d F K S n $.
q3527263-iterates-definition $a |- ( ( Q3527263Iterates K F ) =
  ( iota_ S e. ( ( Base ` K ) ^m NN0 )
    ( ( S ` 0 ) = ( 0. ` K ) /\
      A. n e. NN0
        ( S ` ( n + 1 ) ) = ( F ` ( S ` n ) ) ) ) ) $.

q3527263-kleene-fixed-point-theorem $a |- A. K A. F
  ( ( K e. CLat /\ ( Q3527263OmegaScottContinuous K F ) ) ->
    ( Q3527263Lfp K F ) =
      ( ( lub ` K ) ` ran ( Q3527263Iterates K F ) ) ) $.
