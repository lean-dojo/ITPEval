$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_45
  (verina__metamath__verina_basic_45), catalog title findProduct: the exact
  executable search of an arbitrary finite integer list multiplies its first
  even entry by its first odd entry under the stated existence precondition
  and satisfies the corresponding correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup,
  ran w is its collection of entries, and 0 ..^ ( # ` w ) is its complete
  valid-index set. The Boolean domain is represented by { 0 , 1 }, with
  false = 0 and true = 1.

  VERINAB45IsEven and VERINAB45IsOdd are exactly the source Boolean helpers
  n % 2 = 0 and n % 2 != 0. SetMM integer remainder modulo positive two
  agrees with Lean's nonnegative integer remainder on every integer.
  VERINAB45GetBang reproduces Lean List.get! on integer lists, including its
  inhabited default value zero outside the list.

  VERINAB45FirstEvenIndex and VERINAB45FirstOddIndex select the unique least
  valid indices whose entries have the requested parity. These are exactly
  the successful values of the two source List.findIdx? calls.
  VERINAB45None, VERINAB45Some, VERINAB45PairNat, and
  VERINAB45OptionPair give a disjoint tagged representation of
  Option (Nat x Nat). VERINAB45FirstEvenOddIndices returns the pair of the two
  least indices exactly when both searches succeed and none otherwise,
  preserving the source helper's two-option match.

  VERINAB45IndicesValue extracts the unique pair from a successful helper
  result. VERINAB45FindProduct follows the source match exactly: it multiplies
  the two get!-indexed entries in the some branch and returns zero in the none
  branch. Thus the executable result is fixed independently of the
  postcondition and admits no additional outputs.

  VERINAB45Pre preserves the source length-greater-than-one condition and the
  existence of an even and an odd list entry. VERINAB45Post preserves the
  source match: it is unrestricted in the none branch and requires equality
  with the same indexed product in the some branch. The proof-valued
  precondition arguments to the implementation and postcondition have no
  computational or propositional effect beyond the explicit antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB45IsEven VERINAB45IsOdd VERINAB45GetBang
  VERINAB45None VERINAB45Some VERINAB45PairNat VERINAB45OptionPair
  VERINAB45FirstEvenIndex VERINAB45FirstOddIndex
  VERINAB45FirstEvenOddIndices VERINAB45IndicesValue
  VERINAB45Pre VERINAB45FindProduct VERINAB45Post
$.

verinab45-is-even-syntax
  $a class ( VERINAB45IsEven A ) $.
verinab45-is-odd-syntax
  $a class ( VERINAB45IsOdd A ) $.
verinab45-get-bang-syntax
  $a class ( VERINAB45GetBang A B ) $.
verinab45-none-syntax
  $a class VERINAB45None $.
verinab45-some-syntax
  $a class ( VERINAB45Some A ) $.
verinab45-pair-nat-syntax
  $a class VERINAB45PairNat $.
verinab45-option-pair-syntax
  $a class VERINAB45OptionPair $.
verinab45-first-even-index-syntax
  $a class ( VERINAB45FirstEvenIndex A ) $.
verinab45-first-odd-index-syntax
  $a class ( VERINAB45FirstOddIndex A ) $.
verinab45-first-even-odd-indices-syntax
  $a class ( VERINAB45FirstEvenOddIndices A ) $.
verinab45-indices-value-syntax
  $a class ( VERINAB45IndicesValue A ) $.
verinab45-precondition-syntax
  $a wff ( VERINAB45Pre A ) $.
verinab45-program-syntax
  $a class ( VERINAB45FindProduct A ) $.
verinab45-postcondition-syntax
  $a wff ( VERINAB45Post A B ) $.

verinab45-is-even-definition $a |- (
  VERINAB45IsEven A
) = if (
  ( A mod 2 ) = 0 ,
  1 ,
  0
) $.

verinab45-is-odd-definition $a |- (
  VERINAB45IsOdd A
) = if (
  ( A mod 2 ) =/= 0 ,
  1 ,
  0
) $.

verinab45-get-bang-definition $a |- (
  VERINAB45GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab45-none-definition $a |- VERINAB45None = (/) $.

verinab45-some-definition $a |- (
  VERINAB45Some A
) = <. 1 , A >. $.

verinab45-pair-nat-definition $a |- VERINAB45PairNat = (
  NN0 X. NN0
) $.

${
  $d p x $.

  verinab45-option-pair-definition $a |- VERINAB45OptionPair =
    { x |
      (
        x = VERINAB45None
        \/
        E. p e. VERINAB45PairNat x = ( VERINAB45Some p )
      )
    } $.
$}

${
  $d i j A $.

  verinab45-first-even-index-definition $a |- (
    VERINAB45FirstEvenIndex A
  ) = (
    iota_ i e. ( 0 ..^ ( # ` A ) )
      (
        ( VERINAB45IsEven ( VERINAB45GetBang A i ) ) = 1
        /\
        A. j e. ( 0 ..^ i )
          ( VERINAB45IsEven ( VERINAB45GetBang A j ) ) = 0
      )
  ) $.
$}

${
  $d i j A $.

  verinab45-first-odd-index-definition $a |- (
    VERINAB45FirstOddIndex A
  ) = (
    iota_ i e. ( 0 ..^ ( # ` A ) )
      (
        ( VERINAB45IsOdd ( VERINAB45GetBang A i ) ) = 1
        /\
        A. j e. ( 0 ..^ i )
          ( VERINAB45IsOdd ( VERINAB45GetBang A j ) ) = 0
      )
  ) $.
$}

${
  $d i j A $.

  verinab45-first-even-odd-indices-definition $a |- (
    VERINAB45FirstEvenOddIndices A
  ) = if (
    (
      E. i e. ( 0 ..^ ( # ` A ) )
        ( VERINAB45IsEven ( VERINAB45GetBang A i ) ) = 1
      /\
      E. j e. ( 0 ..^ ( # ` A ) )
        ( VERINAB45IsOdd ( VERINAB45GetBang A j ) ) = 1
    ) ,
    (
      VERINAB45Some
        <.
          ( VERINAB45FirstEvenIndex A ) ,
          ( VERINAB45FirstOddIndex A )
        >.
    ) ,
    VERINAB45None
  ) $.
$}

${
  $d p A $.

  verinab45-indices-value-definition $a |- (
    VERINAB45IndicesValue A
  ) = (
    iota_ p e. VERINAB45PairNat
      (
        ( VERINAB45FirstEvenOddIndices A )
        =
        ( VERINAB45Some p )
      )
  ) $.
$}

${
  $d x y A $.

  verinab45-precondition-definition $a |- (
    VERINAB45Pre A
  ) <-> (
    (
      A e. Word ZZ
      /\
      1 < ( # ` A )
    )
    /\
    (
      E. x e. ran A
        ( VERINAB45IsEven x ) = 1
      /\
      E. y e. ran A
        ( VERINAB45IsOdd y ) = 1
    )
  ) $.
$}

verinab45-program-definition $a |- (
  VERINAB45FindProduct A
) = if (
  ( VERINAB45FirstEvenOddIndices A ) = VERINAB45None ,
  0 ,
  (
    VERINAB45GetBang
      A
      ( 1st ` ( VERINAB45IndicesValue A ) )
  )
  x.
  (
    VERINAB45GetBang
      A
      ( 2nd ` ( VERINAB45IndicesValue A ) )
  )
) $.

verinab45-postcondition-definition $a |- (
  VERINAB45Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    ( VERINAB45FirstEvenOddIndices A ) = VERINAB45None
    \/
    B = (
      (
        VERINAB45GetBang
          A
          ( 1st ` ( VERINAB45IndicesValue A ) )
      )
      x.
      (
        VERINAB45GetBang
          A
          ( 2nd ` ( VERINAB45IndicesValue A ) )
      )
    )
  )
) $.

verina-basic-45-find-product $a |- A. w e. Word ZZ
  (
    ( VERINAB45Pre w )
    ->
    (
      VERINAB45Post
        w
        ( VERINAB45FindProduct w )
    )
  )
$.
