$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_swapqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_lexicographic_permutations_1_Top_swapqtvc):
  the verification condition that swapping two valid positions of an integer
  sequence exchanges their values, preserves every other position, and
  preserves the represented permutation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat and
  NTP4VCAt reproduce the exports' integer-to-natural conversion and totalized
  lookup. NTP4VCSet is the source List.set operation: it has the same finite
  domain as its input word and changes the converted index only when that
  index is in the domain.

  NTP4VCSetFunctionEqual is pointwise equality between the lookup function of
  a list update and the corresponding integer-keyed functional update; by
  function extensionality this is equivalent in both directions to each
  generated function-equality premise. NTP4VCOcc and NTP4VCPerm directly
  encode full-sequence occurrence counting and is_permutation_of over every
  integer value. The Why3 to_seq operation is replaced by the same finite
  word: its specification gives equal length and equality at every valid
  index, hence finite-word extensionality gives equality in both directions.

  The let-bound temporary values and sequential updates are represented by
  NTP4VCAfterFirst and NTP4VCSwapped. NTP4VCSwapVC retains every conjunction
  and both right-associated implication chains of the generated verification
  condition. The source typed parameters and four assumptions remain separate
  essential hypotheses. Every auxiliary $a declaration is syntax or an
  explicit faithful definition. The final $a declaration is Metamath's native
  unproved statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCAfterFirst NTP4VCSwapped
  NTP4VCOcc NTP4VCPerm NTP4VCSetFunctionEqual NTP4VCOther
  NTP4VCSwapFinal NTP4VCSwapVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-after-first-syntax
  $a class ( NTP4VCAfterFirst A B C ) $.
ntp4vc-swapped-syntax
  $a class ( NTP4VCSwapped A B C ) $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B ) $.

ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-set-function-equal-syntax
  $a wff ( NTP4VCSetFunctionEqual A B C ) $.
ntp4vc-other-syntax
  $a wff ( NTP4VCOther A B C D ) $.
ntp4vc-swap-final-syntax
  $a wff ( NTP4VCSwapFinal A B C D ) $.
ntp4vc-swap-vc-syntax
  $a wff ( NTP4VCSwapVC A B C ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

ntp4vc-after-first-definition $a |- (
  NTP4VCAfterFirst A B C
) = (
  NTP4VCSet
    A
    B
    ( NTP4VCAt A C )
) $.

ntp4vc-swapped-definition $a |- (
  NTP4VCSwapped A B C
) = (
  NTP4VCSet
    ( NTP4VCAfterFirst A B C )
    C
    ( NTP4VCAt A B )
) $.

${
  $d k A B $.

  ntp4vc-occ-definition $a |- (
    NTP4VCOcc A B
  ) = (
    # `
    { k e. ZZ |
      (
        (
          0 <_ k
          /\
          k < ( # ` A )
        )
        /\
        ( NTP4VCAt A k ) = B
      )
    }
  ) $.
$}

${
  $d v A B $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. ZZ
        (
          ( NTP4VCOcc A v )
          =
          ( NTP4VCOcc B v )
        )
    )
  ) $.
$}

${
  $d x A B C $.

  ntp4vc-set-function-equal-definition $a |- (
    NTP4VCSetFunctionEqual A B C
  ) <->
  A. x e. ZZ
    (
      ( NTP4VCAt ( NTP4VCSet A B C ) x )
      =
      if (
        x = B ,
        C ,
        ( NTP4VCAt A x )
      )
    ) $.
$}

${
  $d k A B C D $.

  ntp4vc-other-definition $a |- (
    NTP4VCOther A B C D
  ) <->
  A. k e. ZZ
    (
      (
        0 <_ k
        /\
        k < ( # ` A )
      )
      ->
      (
        k =/= C
        ->
        (
          k =/= D
          ->
          ( NTP4VCAt A k ) = ( NTP4VCAt B k )
        )
      )
    ) $.
$}

ntp4vc-swap-final-definition $a |- (
  NTP4VCSwapFinal A B C D
) <->
(
  (
    ( NTP4VCAt A C ) = ( NTP4VCAt B D )
    /\
    ( NTP4VCAt A D ) = ( NTP4VCAt B C )
  )
  /\
  (
    ( NTP4VCOther A B C D )
    /\
    ( NTP4VCPerm A B )
  )
) $.

ntp4vc-swap-vc-definition $a |- (
  NTP4VCSwapVC A B C
) <->
(
  0 <_ B
  /\
  (
    B < ( # ` A )
    /\
    (
      (
        0 <_ C
        /\
        C < ( # ` A )
      )
      /\
      (
        (
          0 <_ B
          /\
          B < ( # ` A )
        )
        /\
        (
          (
            ( # ` ( NTP4VCAfterFirst A B C ) )
            =
            ( # ` A )
          )
          ->
          (
            ( NTP4VCSetFunctionEqual
                A
                B
                ( NTP4VCAt A C )
            )
            ->
            (
              (
                0 <_ C
                /\
                C < ( # ` ( NTP4VCAfterFirst A B C ) )
              )
              /\
              (
                (
                  ( # ` ( NTP4VCSwapped A B C ) )
                  =
                  ( # ` ( NTP4VCAfterFirst A B C ) )
                )
                ->
                (
                  ( NTP4VCSetFunctionEqual
                      ( NTP4VCAfterFirst A B C )
                      C
                      ( NTP4VCAt A B )
                  )
                  ->
                  ( NTP4VCSwapFinal
                      ( NTP4VCSwapped A B C )
                      A
                      B
                      C
                  )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

${
  $d k v x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source theorem parameters a, i, and j. $)
  ntp4vc-a-word $e |- A e. Word ZZ $.
  ntp4vc-i-int $e |- B e. ZZ $.
  ntp4vc-j-int $e |- C e. ZZ $.

  $( Source assumptions fact0 through fact3. $)
  ntp4vc-fact0 $e |- 0 <_ B $.
  ntp4vc-fact1 $e |- B < ( # ` A ) $.
  ntp4vc-fact2 $e |- 0 <_ C $.
  ntp4vc-fact3 $e |- C < ( # ` A ) $.

  ntp4vc-pearl-verifythis-2021-lexicographic-permutations-1-top-swap-vc
    $a |- ( NTP4VCSwapVC A B C ) $.
$}
