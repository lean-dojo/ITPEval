$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_93
  (verina__metamath__verina_basic_93), catalog title SwapBitvectors: the exact
  executable three-XOR computation swaps two 8-bit unsigned integers as an
  ordered pair and satisfies its component and changed-position correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB93UInt8 is exactly the 256-element unsigned 8-bit domain
  0 ..^ 2^8. For a natural A and bit position B, VERINAB93Bit A B is
  floor(A / 2^B) modulo two. VERINAB93Xor reconstructs the unique 8-bit word
  whose bit at each position below eight differs exactly when the
  corresponding input bits differ. Thus it is definitionally the source
  UInt8.xor operation on VERINAB93UInt8.

  VERINAB93Temp, VERINAB93NewY, and VERINAB93NewX preserve the source
  let-bound sequence exactly: temp is X xor Y, newY is temp xor Y, and newX
  is temp xor newY. VERINAB93SwapBitvectors returns exactly the ordered pair
  (newX,newY), so the executable result is fixed independently of the
  postcondition and admits no additional output.

  VERINAB93Pre is the source True precondition together with both UInt8 input
  types. VERINAB93Post preserves both component equations and the conditional
  clause that unequal inputs leave each returned component unequal to the
  input formerly occupying that position. The proof-valued precondition
  arguments to the implementation and postcondition are computationally and
  propositionally unused beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this artifact adds no $p
  declaration.
$)

$c
  VERINAB93UInt8 VERINAB93Bit VERINAB93Xor
  VERINAB93Temp VERINAB93NewY VERINAB93NewX
  VERINAB93Pre VERINAB93SwapBitvectors VERINAB93Post
$.

verinab93-uint8-syntax
  $a class VERINAB93UInt8 $.
verinab93-bit-syntax
  $a class ( VERINAB93Bit A B ) $.
verinab93-xor-syntax
  $a class ( VERINAB93Xor A B ) $.
verinab93-temp-syntax
  $a class ( VERINAB93Temp A B ) $.
verinab93-new-y-syntax
  $a class ( VERINAB93NewY A B ) $.
verinab93-new-x-syntax
  $a class ( VERINAB93NewX A B ) $.
verinab93-precondition-syntax
  $a wff ( VERINAB93Pre A B ) $.
verinab93-program-syntax
  $a class ( VERINAB93SwapBitvectors A B ) $.
verinab93-postcondition-syntax
  $a wff ( VERINAB93Post A B C ) $.

verinab93-uint8-definition $a |- VERINAB93UInt8 =
  ( 0 ..^ ( 2 ^ 8 ) ) $.

verinab93-bit-definition $a |- (
  VERINAB93Bit A B
) = (
  ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2
) $.

${
  $d k A B $.

  verinab93-xor-definition $a |- (
    VERINAB93Xor A B
  ) = (
    sum_ k e. ( 0 ..^ 8 )
      if (
        ( VERINAB93Bit A k ) = ( VERINAB93Bit B k ) ,
        0 ,
        ( 2 ^ k )
      )
  ) $.
$}

verinab93-temp-definition $a |- (
  VERINAB93Temp A B
) = (
  VERINAB93Xor A B
) $.

verinab93-new-y-definition $a |- (
  VERINAB93NewY A B
) = (
  VERINAB93Xor
    ( VERINAB93Temp A B )
    B
) $.

verinab93-new-x-definition $a |- (
  VERINAB93NewX A B
) = (
  VERINAB93Xor
    ( VERINAB93Temp A B )
    ( VERINAB93NewY A B )
) $.

verinab93-precondition-definition $a |- (
  VERINAB93Pre A B
) <-> (
  A e. VERINAB93UInt8
  /\
  B e. VERINAB93UInt8
) $.

verinab93-program-definition $a |- (
  VERINAB93SwapBitvectors A B
) = <.
  ( VERINAB93NewX A B ) ,
  ( VERINAB93NewY A B )
>. $.

verinab93-postcondition-definition $a |- (
  VERINAB93Post A B C
) <-> (
  (
    (
      A e. VERINAB93UInt8
      /\
      B e. VERINAB93UInt8
    )
    /\
    C e. ( VERINAB93UInt8 X. VERINAB93UInt8 )
  )
  /\
  (
    ( 1st ` C ) = B
    /\
    (
      ( 2nd ` C ) = A
      /\
      (
        A =/= B
        ->
        (
          ( 1st ` C ) =/= A
          /\
          ( 2nd ` C ) =/= B
        )
      )
    )
  )
) $.

verina-basic-93-swap-bitvectors $a |- A. x e. VERINAB93UInt8
  A. y e. VERINAB93UInt8
    (
      ( VERINAB93Pre x y )
      ->
      (
        VERINAB93Post
          x
          y
          ( VERINAB93SwapBitvectors x y )
      )
    )
$.
