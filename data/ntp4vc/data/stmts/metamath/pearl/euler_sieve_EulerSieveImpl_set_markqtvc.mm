$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieveImpl_set_markqtvc: the Euler-sieve set-mark
  verification condition updates an odd marked position and, when necessary,
  negates the corresponding compressed-array entry while preserving the full
  sieve-state invariant. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A and B below are arbitrary nonempty carriers for ArrayInt63.array63 and the
  sieve state type. Their elts, size, nexts, marked, arr, max, and max_arr
  accessors remain arbitrary total functions subject to exactly the source
  universal invariants and state extensionality axiom.

  NTP4VCBV63 is the exact signed-63-bit integer interval. Integer and Boolean
  lists are full SetMM words over ZZ and 2, with false=0 and true=1.
  NTP4VCAtInt and NTP4VCAtBool reproduce the source totalized list lookups,
  and NTP4VCSet reproduces List.set after Int.toNat. NTP4VCTDiv2 is signed
  division by two truncated toward zero; NTP4VCEdiv2 is floor division by
  two, used only where the source operands are nonnegative.

  The named predicates factor, without weakening, the array invariant, the
  complete sieve-state invariant, both branches of the proposition-valued
  conditional, both list-update laws, the abstract array-update witnesses,
  and the final universal state obligation. Expanding their biconditional
  definitions recovers every source domain, quantifier, assumption, repeated
  bound, and conclusion. The final declaration is Metamath's native unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCIn63 NTP4VCBV63 NTP4VCToNat
  NTP4VCAtInt NTP4VCAtBool NTP4VCSet
  NTP4VCTDiv2 NTP4VCEdiv2 NTP4VCAbs NTP4VCBound
  NTP4VCInvNexts NTP4VCAllEliminated
  NTP4VCArrayInv NTP4VCParityInv NTP4VCArrayState
  NTP4VCJumpInv NTP4VCStateInv
  NTP4VCResult NTP4VCMarking NTP4VCPositive NTP4VCEntry
$.

ntp4vc-in63-syntax $a wff ( NTP4VCIn63 A ) $.
ntp4vc-bv63-syntax $a class NTP4VCBV63 $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-int-syntax $a class ( NTP4VCAtInt A B ) $.
ntp4vc-at-bool-syntax $a class ( NTP4VCAtBool A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-tdiv2-syntax $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-ediv2-syntax $a class ( NTP4VCEdiv2 A ) $.
ntp4vc-abs-syntax $a class ( NTP4VCAbs A ) $.
ntp4vc-bound-syntax $a wff ( NTP4VCBound A B ) $.
ntp4vc-inv-nexts-syntax $a wff ( NTP4VCInvNexts A B ) $.
ntp4vc-all-eliminated-syntax
  $a wff ( NTP4VCAllEliminated A B ) $.
ntp4vc-array-inv-syntax $a wff ( NTP4VCArrayInv A B ) $.
ntp4vc-parity-inv-syntax
  $a wff ( NTP4VCParityInv A B C ) $.
ntp4vc-array-state-syntax
  $a wff ( NTP4VCArrayState A B C D E ) $.
ntp4vc-jump-inv-syntax $a wff ( NTP4VCJumpInv A B C ) $.
ntp4vc-state-inv-syntax
  $a wff ( NTP4VCStateInv A B C D E ) $.
ntp4vc-result-syntax
  $a wff ( NTP4VCResult A B C D E F G H I J K L M ) $.
ntp4vc-marking-syntax
  $a wff ( NTP4VCMarking A B C D E F G H I J K L ) $.
ntp4vc-positive-syntax
  $a wff ( NTP4VCPositive A B C D E F G H I J K L M ) $.
ntp4vc-entry-syntax
  $a wff ( NTP4VCEntry A B C D E F G H I J K L ) $.

ntp4vc-in63-definition $a |- (
  ( NTP4VCIn63 A )
  <->
  (
    ( -u ( 2 ^ ; 6 2 ) ) <_ A
    /\
    A < ( 2 ^ ; 6 2 )
  )
) $.

ntp4vc-bv63-definition $a |- NTP4VCBV63 = {
  x e. ZZ | ( NTP4VCIn63 x )
} $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-int-definition $a |- (
  NTP4VCAtInt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-at-bool-definition $a |- (
  NTP4VCAtBool A B
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

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-ediv2-definition $a |- (
  NTP4VCEdiv2 A
) = ( |_ ` ( A / 2 ) ) $.

ntp4vc-abs-definition $a |- (
  NTP4VCAbs A
) = if (
  A < 0 ,
  ( -u A ) ,
  A
) $.

ntp4vc-bound-definition $a |- (
  ( NTP4VCBound A B )
  <->
  (
    0 <_ B
    /\
    B < ( # ` A )
  )
) $.

${
  $d i A B $.

  ntp4vc-inv-nexts-definition $a |- (
    ( NTP4VCInvNexts A B )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        (
          i < ( NTP4VCAtInt A i )
          /\
          ( NTP4VCAtInt A i ) <_ B
        )
      )
  ) $.
$}

${
  $d i j A B $.

  ntp4vc-all-eliminated-definition $a |- (
    ( NTP4VCAllEliminated A B )
    <->
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          ->
          A. j e. ZZ
            (
              (
                i < j
                /\
                j < ( NTP4VCAtInt B i )
              )
              ->
              ( NTP4VCAtBool A j ) = 1
            )
        )
    )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-array-inv-definition $a |- (
    ( NTP4VCArrayInv A B )
    <->
    (
      0 <_ B
      /\
      (
        B = ( # ` A )
        /\
        (
          ( # ` A ) < ( 2 ^ ; 6 2 )
          /\
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < ( # ` A )
              )
              ->
              ( NTP4VCIn63 ( NTP4VCAtInt A i ) )
            )
        )
      )
    )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-parity-inv-definition $a |- (
    ( NTP4VCParityInv A B C )
    <->
    (
      A. i e. ZZ
        (
          (
            3 <_ i
            /\
            i <_ C
          )
          ->
          (
            ( i mod 2 ) = 0
            ->
            ( NTP4VCAtBool A i ) = 1
          )
        )
      /\
      (
        A. i e. ZZ
          (
            (
              3 <_ i
              /\
              i < ( C - 1 )
            )
            ->
            (
              ( i mod 2 ) = 1
              ->
              (
                ( ( NTP4VCAtInt B i ) mod 2 ) = 1
                \/
                ( NTP4VCAtInt B i ) = ( C + 1 )
              )
            )
          )
        /\
        (
          ( NTP4VCAtInt B C ) = ( C + 1 )
          /\
          (
            (
              ( ( C - 1 ) mod 2 ) = 0
              ->
              ( NTP4VCAtInt B ( C - 1 ) ) = C
            )
            /\
            (
              ( ( C - 1 ) mod 2 ) = 1
              ->
              ( NTP4VCAtInt B ( C - 1 ) ) = ( C + 1 )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-array-state-definition $a |- (
    ( NTP4VCArrayState A B C D E )
    <->
    (
      ( # ` A ) = ( E + 1 )
      /\
      (
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i <_ E
            )
            ->
            (
              ( -u ( D + 1 ) ) <_ ( NTP4VCAtInt A i )
              /\
              ( NTP4VCAtInt A i ) <_ ( D + 1 )
            )
          )
        /\
        (
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i <_ E
              )
              ->
              (
                ( NTP4VCAtBool C ( ( 2 x. i ) + 1 ) ) = 1
                <->
                ( NTP4VCAtInt A i ) < 0
              )
            )
          /\
          (
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i <_ E
                )
                ->
                (
                  -. ( NTP4VCAtBool C ( ( 2 x. i ) + 1 ) ) = 1
                  ->
                  ( NTP4VCAtInt A i ) =
                    ( NTP4VCAtInt B ( ( 2 x. i ) + 1 ) )
                )
              )
            /\
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i <_ E
                )
                ->
                (
                  ( NTP4VCAtBool C ( ( 2 x. i ) + 1 ) ) = 1
                  ->
                  ( NTP4VCAtInt A i ) =
                    ( -u ( NTP4VCAtInt B ( ( 2 x. i ) + 1 ) ) )
                )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d i j A B C $.

  ntp4vc-jump-inv-definition $a |- (
    ( NTP4VCJumpInv A B C )
    <->
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i <_ C
          )
          ->
          (
            (
              i < ( NTP4VCEdiv2 ( NTP4VCAbs ( NTP4VCAtInt A i ) ) )
              /\
              ( NTP4VCEdiv2 ( NTP4VCAbs ( NTP4VCAtInt A i ) ) )
                <_ ( C + 1 )
            )
            /\
            ( NTP4VCAbs ( NTP4VCAtInt A i ) ) <_ ( B + 1 )
          )
        )
      /\
      A. i e. ZZ A. j e. ZZ
        (
          (
            0 <_ i
            /\
            i <_ C
          )
          ->
          (
            (
              i < j
              /\
              j < ( NTP4VCEdiv2 ( NTP4VCAbs ( NTP4VCAtInt A i ) ) )
            )
            ->
            ( NTP4VCAtInt A j ) < 0
          )
        )
    )
  ) $.
$}

ntp4vc-state-inv-definition $a |- (
  ( NTP4VCStateInv A B C D E )
  <->
  (
    D < ( ( 2 ^ ; 6 2 ) - 1 )
    /\
    (
      3 <_ D
      /\
      (
        ( # ` A ) = ( # ` B )
        /\
        (
          ( # ` B ) = ( D + 1 )
          /\
          (
            ( NTP4VCEdiv2 ( D - 1 ) ) = E
            /\
            (
              ( NTP4VCInvNexts A ( # ` A ) )
              /\
              (
                ( NTP4VCAllEliminated B A )
                /\
                (
                  ( NTP4VCParityInv B A D )
                  /\
                  (
                    ( NTP4VCArrayState C A B D E )
                    /\
                    ( NTP4VCJumpInv C D E )
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
  $d t A B C D E F G H I J K L M $.

  ntp4vc-result-definition $a |- (
    ( NTP4VCResult A B C D E F G H I J K L M )
    <->
    A. t e. B
      (
        ( NTP4VCStateInv ( E ` J ) K ( C ` L ) ( H ` J ) ( I ` J ) )
        /\
        (
          (
            ( I ` J ) = ( I ` t )
            /\
            (
              ( H ` J ) = ( H ` t )
              /\
              (
                L = ( G ` t )
                /\
                (
                  K = ( F ` t )
                  /\
                  ( E ` J ) = ( E ` t )
                )
              )
            )
          )
          ->
          ( F ` t ) = ( NTP4VCSet ( F ` J ) M 1 )
        )
      )
  ) $.
$}

${
  $d j A B C D E F G H I J K L $.

  ntp4vc-marking-definition $a |- (
    ( NTP4VCMarking A B C D E F G H I J K L )
    <->
    (
      ( NTP4VCBound ( F ` J ) L )
      /\
      (
        (
          ( # ` ( NTP4VCSet ( F ` J ) L 1 ) ) = ( # ` ( F ` J ) )
          /\
          (
            ( NTP4VCAtBool ( NTP4VCSet ( F ` J ) L 1 ) L ) = 1
            /\
            A. j e. ZZ
              (
                (
                  (
                    0 <_ j
                    /\
                    j < ( # ` ( F ` J ) )
                  )
                  /\
                  -. j = L
                )
                ->
                ( NTP4VCAtBool ( NTP4VCSet ( F ` J ) L 1 ) j )
                  = ( NTP4VCAtBool ( F ` J ) j )
              )
          )
        )
        ->
        (
          NTP4VCResult
            A B C D E F G H I J
            ( NTP4VCSet ( F ` J ) L 1 ) K L
        )
      )
    )
  ) $.
$}

${
  $d a q A B C D E F G H I J K L M $.

  ntp4vc-positive-definition $a |- (
    ( NTP4VCPositive A B C D E F G H I J K L M )
    <->
    (
      ( NTP4VCIn63 ( -u L ) )
      /\
      A. q e. NTP4VCBV63
        (
          q = ( -u L )
          ->
          (
            ( NTP4VCBound ( C ` ( G ` J ) ) K )
            /\
            A. a e. A
              (
                (
                  ( D ` a ) = ( D ` ( G ` J ) )
                  /\
                  (
                    ( D ` a ) = ( D ` ( G ` J ) )
                    /\
                    ( C ` a ) =
                      ( NTP4VCSet ( C ` ( G ` J ) ) K q )
                  )
                )
                ->
                (
                  NTP4VCMarking
                    A B C D E F G H I J a M
                )
              )
          )
        )
    )
  ) $.
$}

${
  $d o q A B C D E F G H I J K L $.

  ntp4vc-entry-definition $a |- (
    ( NTP4VCEntry A B C D E F G H I J K L )
    <->
    A. o e. NTP4VCBV63
      (
        o = ( NTP4VCAtInt ( C ` ( G ` J ) ) K )
        ->
        (
          (
            0 <_ o
            /\
            (
              ( NTP4VCBound ( C ` ( G ` J ) ) K )
              /\
              A. q e. NTP4VCBV63
                (
                  q = ( NTP4VCAtInt ( C ` ( G ` J ) ) K )
                  ->
                  (
                    NTP4VCPositive
                      A B C D E F G H I J K q L
                  )
                )
            )
          )
          \/
          (
            -. 0 <_ o
            /\
            (
              NTP4VCMarking
                A B C D E F G H I J ( G ` J ) L
            )
          )
        )
      )
  ) $.
$}

${
  $d a b t x A B C D E F G H I J K $.

  $( Source abstract carriers. $)
  ntp4vc-array-carrier-nonempty $e |- A =/= (/) $.
  ntp4vc-state-carrier-nonempty $e |- B =/= (/) $.

  $( Source accessors and their exact full domains/codomains. $)
  ntp4vc-elts-function $e |- C e. ( ( Word ZZ ) ^m A ) $.
  ntp4vc-size-function $e |- D e. ( ZZ ^m A ) $.
  ntp4vc-nexts-function $e |- E e. ( ( Word ZZ ) ^m B ) $.
  ntp4vc-marked-function $e |- F e. ( ( Word 2 ) ^m B ) $.
  ntp4vc-arr-function $e |- G e. ( A ^m B ) $.
  ntp4vc-max-function $e |- H e. ( NTP4VCBV63 ^m B ) $.
  ntp4vc-max-arr-function $e |- I e. ( NTP4VCBV63 ^m B ) $.

  $( Universal source invariants and state extensionality/injectivity. $)
  ntp4vc-array-invariant $e |- A. a e. A
    ( NTP4VCArrayInv ( C ` a ) ( D ` a ) ) $.

  ntp4vc-state-invariant $e |- A. t e. B
    (
      NTP4VCStateInv
        ( E ` t ) ( F ` t ) ( C ` ( G ` t ) ) ( H ` t ) ( I ` t )
    ) $.

  ntp4vc-state-injective $e |- A. a e. B A. b e. B
    (
      (
        ( E ` a ) = ( E ` b )
        /\
        (
          ( F ` a ) = ( F ` b )
          /\
          (
            ( G ` a ) = ( G ` b )
            /\
            (
              ( H ` a ) = ( H ` b )
              /\
              ( I ` a ) = ( I ` b )
            )
          )
        )
      )
      ->
      a = b
    ) $.

  $( Source theorem parameters and facts. $)
  ntp4vc-index-word $e |- J e. NTP4VCBV63 $.
  ntp4vc-state-parameter $e |- K e. B $.
  ntp4vc-index-nonnegative $e |- 0 <_ J $.
  ntp4vc-index-at-most-max $e |- J <_ ( H ` K ) $.
  ntp4vc-index-odd $e |- ( J mod 2 ) = 1 $.

  ntp4vc-pearl-euler-sieve-set-mark-vc $a |- (
    2 =/= 0
    /\
    (
      ( NTP4VCIn63 ( NTP4VCTDiv2 J ) )
      /\
      A. x e. NTP4VCBV63
        (
          x = ( NTP4VCTDiv2 J )
          ->
          (
            ( NTP4VCBound ( C ` ( G ` K ) ) x )
            /\
            (
              NTP4VCEntry
                A B C D E F G H I K x J
            )
          )
        )
    )
  ) $.
$}
