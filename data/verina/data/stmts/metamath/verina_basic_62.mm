$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_62
  (verina__metamath__verina_basic_62), catalog title Find: the exact
  executable left-to-right linear search of an arbitrary finite integer array
  returns its first matching index, or integer -1 when the key is absent, and
  satisfies its complete correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  m ..^ n is the half-open natural interval from m through n - 1.

  VERINAB62GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB62ToNat is
  exactly Lean Int.toNat, returning zero on negative integers.

  VERINAB62Search is the exact result of the source local recursive helper for
  every typed array, integer key, and natural starting index. If the suffix
  from that index contains the key, it returns the unique least matching
  index; otherwise it returns -1. This is precisely the source branch order:
  each unequal in-bounds entry advances by one, the first equal entry returns
  its index via Int.ofNat, and reaching the array size returns -1.
  VERINAB62Find invokes this helper at zero, so the executable result is fixed
  independently of the postcondition and admits no additional outputs.

  VERINAB62Pre is the source True precondition on typed inputs.
  VERINAB62Post preserves all three source conjuncts: the result is -1 or an
  in-bounds nonnegative integer; a result different from -1 indexes the key
  and has no earlier matching index; and -1 means no valid array index
  contains the key.
  Natural numbers embed into SetMM integers exactly as Lean Int.ofNat. The
  proof-valued precondition arguments to the implementation and postcondition
  are computationally and propositionally unused beyond the explicit
  precondition antecedent in the final correctness assertion. Every earlier
  $a is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB62GetBang VERINAB62ToNat
  VERINAB62Pre VERINAB62Search VERINAB62Find VERINAB62Post
$.

verinab62-get-bang-syntax
  $a class ( VERINAB62GetBang A B ) $.
verinab62-to-nat-syntax
  $a class ( VERINAB62ToNat A ) $.
verinab62-precondition-syntax
  $a wff ( VERINAB62Pre A B ) $.
verinab62-search-syntax
  $a class ( VERINAB62Search A B C ) $.
verinab62-program-syntax
  $a class ( VERINAB62Find A B ) $.
verinab62-postcondition-syntax
  $a wff ( VERINAB62Post A B C ) $.

verinab62-get-bang-definition $a |- (
  VERINAB62GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab62-to-nat-definition $a |- (
  VERINAB62ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

verinab62-precondition-definition $a |- (
  VERINAB62Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. ZZ
) $.

${
  $d i j A B C $.

  verinab62-search-definition $a |- (
    VERINAB62Search A B C
  ) = if (
    E. i e. ( C ..^ ( # ` A ) )
      ( A ` i ) = B ,
    iota_ i e. ( C ..^ ( # ` A ) )
      (
        ( A ` i ) = B
        /\
        A. j e. ( C ..^ i )
          ( A ` j ) =/= B
      ) ,
    ( -u 1 )
  ) $.
$}

verinab62-program-definition $a |- (
  VERINAB62Find A B
) = (
  VERINAB62Search A B 0
) $.

${
  $d i A B C $.

  verinab62-postcondition-definition $a |- (
    VERINAB62Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. ZZ
    )
    /\
    (
      (
        C = ( -u 1 )
        \/
        (
          0 <_ C
          /\
          C < ( # ` A )
        )
      )
      /\
      (
        (
          C =/= ( -u 1 )
          ->
          (
            (
              VERINAB62GetBang A ( VERINAB62ToNat C )
            ) = B
            /\
            A. i e. NN0
              (
                i < ( VERINAB62ToNat C )
                ->
                ( VERINAB62GetBang A i ) =/= B
              )
          )
        )
        /\
        (
          C = ( -u 1 )
          ->
          A. i e. NN0
            (
              i < ( # ` A )
              ->
              ( VERINAB62GetBang A i ) =/= B
            )
        )
      )
    )
  ) $.
$}

verina-basic-62-find $a |- A. w e. Word ZZ
  A. k e. ZZ
    (
      ( VERINAB62Pre w k )
      ->
      (
        VERINAB62Post
          w
          k
          ( VERINAB62Find w k )
      )
    )
$.
