$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_permutqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_lexicographic_permutations_1_Top_permutqtvc):
  the verification condition that enumerating all permutations of an integer
  sequence by repeated lexicographic successor produces exactly the
  permutations, in strict lexicographic order. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, Word ZZ is the type of
  arbitrary finite zero-based integer sequences, and Word ( Word ZZ ) is the
  corresponding type of finite sequences of permutations. NTP4VCFSet is the
  exact class of finite subsets of Word ZZ. The abstract function H represents
  the source all_permutations operation; its type and its full inclusion
  contract are retained as essential hypotheses.

  NTP4VCToNat, NTP4VCAt, NTP4VCOcc, NTP4VCPerm, and NTP4VCLexLT directly
  encode the primary Why3 integer conversion, totalized lookup, occurrence
  count, permutation relation, and strict lexicographic order. The Why3
  to_seq operation is replaced by the same finite word: its specification
  gives equal length and equality at every valid index, so finite-word
  extensionality gives equality in both directions. NTP4VCSnoc is the exact
  finite-word append operation, making the generated copy and append
  specifications definitional.

  The remaining named predicates are biconditional factorizations of the
  sortedness assumption, loop invariant, next-permutation contract, variant
  decrease, success and termination branches, and final enumeration
  postcondition. Expanding them recovers all source domains, quantifier
  scopes, assumptions, and conclusions. Boolean results use the exact
  two-element set { 0, 1 }, with 0 false and 1 true.

  Every auxiliary $a declaration is syntax or an explicit faithful
  definition. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSeqAt NTP4VCSnoc NTP4VCFSet NTP4VCOcc
  NTP4VCPerm NTP4VCLexLT NTP4VCAscending NTP4VCAllResultPerms
  NTP4VCStrictOrder NTP4VCBeforeLast NTP4VCSetEnumerates NTP4VCLoopInv
  NTP4VCUnchanged NTP4VCNoGreater NTP4VCNoBetween NTP4VCNextContract
  NTP4VCVariantDecrease NTP4VCSuccess NTP4VCFinal NTP4VCLoopStep
  NTP4VCLoopObligation NTP4VCAfterSort NTP4VCPermutVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-seq-at-syntax
  $a class ( NTP4VCSeqAt A B ) $.
ntp4vc-snoc-syntax
  $a class ( NTP4VCSnoc A B ) $.
ntp4vc-fset-syntax
  $a class NTP4VCFSet $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B ) $.

ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-lex-lt-syntax
  $a wff ( NTP4VCLexLT A B ) $.
ntp4vc-ascending-syntax
  $a wff ( NTP4VCAscending A ) $.
ntp4vc-all-result-perms-syntax
  $a wff ( NTP4VCAllResultPerms A B ) $.
ntp4vc-strict-order-syntax
  $a wff ( NTP4VCStrictOrder A ) $.
ntp4vc-before-last-syntax
  $a wff ( NTP4VCBeforeLast A B C ) $.
ntp4vc-set-enumerates-syntax
  $a wff ( NTP4VCSetEnumerates A B ) $.
ntp4vc-loop-inv-syntax
  $a wff ( NTP4VCLoopInv A B C D E ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B ) $.
ntp4vc-no-greater-syntax
  $a wff ( NTP4VCNoGreater A B ) $.
ntp4vc-no-between-syntax
  $a wff ( NTP4VCNoBetween A B C ) $.
ntp4vc-next-contract-syntax
  $a wff ( NTP4VCNextContract A B C D ) $.
ntp4vc-variant-decrease-syntax
  $a wff ( NTP4VCVariantDecrease A B C ) $.
ntp4vc-success-syntax
  $a wff ( NTP4VCSuccess A B C D E ) $.
ntp4vc-final-syntax
  $a wff ( NTP4VCFinal A B ) $.
ntp4vc-loop-step-syntax
  $a wff ( NTP4VCLoopStep A B C D E F G ) $.
ntp4vc-loop-obligation-syntax
  $a wff ( NTP4VCLoopObligation A B C D ) $.
ntp4vc-after-sort-syntax
  $a wff ( NTP4VCAfterSort A B C ) $.
ntp4vc-permut-vc-syntax
  $a wff ( NTP4VCPermutVC A B ) $.

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

ntp4vc-seq-at-definition $a |- (
  NTP4VCSeqAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  (/) 
) $.

${
  $d k A B $.

  ntp4vc-snoc-definition $a |- (
    NTP4VCSnoc A B
  ) = (
    k e. ( 0 ..^ ( ( # ` A ) + 1 ) ) |->
      if (
        k < ( # ` A ) ,
        ( A ` k ) ,
        B
      )
  ) $.
$}

${
  $d x A $.

  ntp4vc-fset-definition $a |- NTP4VCFSet = {
    x e. Fin | x C_ Word ZZ
  } $.
$}

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
  $d i j A B $.

  ntp4vc-lex-lt-definition $a |- (
    NTP4VCLexLT A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      (
        ( # ` A ) = ( # ` B )
        /\
        0 < ( # ` A )
      )
      /\
      E. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          /\
          (
            A. j e. ZZ
              (
                (
                  0 <_ j
                  /\
                  j < i
                )
                ->
                ( NTP4VCAt A j ) = ( NTP4VCAt B j )
              )
            /\
            ( NTP4VCAt A i ) < ( NTP4VCAt B i )
          )
        )
    )
  ) $.
$}

${
  $d i j A $.

  ntp4vc-ascending-definition $a |- (
    NTP4VCAscending A
  ) <->
  (
    A e. Word ZZ
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            0 <_ i
            /\
            (
              i <_ j
              /\
              j < ( # ` A )
            )
          )
          ->
          ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
        )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-all-result-perms-definition $a |- (
    NTP4VCAllResultPerms A B
  ) <->
  (
    (
      A e. Word ( Word ZZ )
      /\
      B e. Word ZZ
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` A )
        )
        ->
        (
          NTP4VCPerm
            ( NTP4VCSeqAt A i )
            B
        )
      )
  ) $.
$}

${
  $d i j A $.

  ntp4vc-strict-order-definition $a |- (
    NTP4VCStrictOrder A
  ) <->
  (
    A e. Word ( Word ZZ )
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            0 <_ i
            /\
            (
              i < j
              /\
              j < ( # ` A )
            )
          )
          ->
          (
            NTP4VCLexLT
              ( NTP4VCSeqAt A i )
              ( NTP4VCSeqAt A j )
          )
        )
  ) $.
$}

${
  $d i p A B C $.

  ntp4vc-before-last-definition $a |- (
    NTP4VCBeforeLast A B C
  ) <->
  (
    (
      A e. Word ( Word ZZ )
      /\
      (
        B e. Word ZZ
        /\
        C e. Word ZZ
      )
    )
    /\
    A. p e. Word ZZ
      (
        (
          ( NTP4VCPerm p B )
          /\
          ( NTP4VCLexLT p C )
        )
        ->
        E. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < ( ( # ` A ) - 1 )
            )
            /\
            ( NTP4VCSeqAt A i ) = p
          )
      )
  ) $.
$}

${
  $d i p A B $.

  ntp4vc-set-enumerates-definition $a |- (
    NTP4VCSetEnumerates A B
  ) <->
  (
    (
      A e. NTP4VCFSet
      /\
      B e. Word ( Word ZZ )
    )
    /\
    A. p e. Word ZZ
      (
        p e. A
        <->
        E. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < ( # ` B )
            )
            /\
            ( NTP4VCSeqAt B i ) = p
          )
      )
  ) $.
$}

ntp4vc-loop-inv-definition $a |- (
  NTP4VCLoopInv A B C D E
) <->
(
  (
    A e. NTP4VCFSet
    /\
    (
      B e. Word ZZ
      /\
      C e. Word ZZ
    )
  )
  /\
  (
    (
      D e. Word ( Word ZZ )
      /\
      E e. NTP4VCFSet
    )
    /\
    (
      0 < ( # ` D )
      /\
      (
        ( NTP4VCPerm C B )
        /\
        (
          ( NTP4VCAllResultPerms D B )
          /\
          (
            (
              NTP4VCSeqAt
                D
                ( ( # ` D ) - 1 )
            ) = C
            /\
            (
              NTP4VCPerm
                (
                  NTP4VCSeqAt
                    D
                    ( ( # ` D ) - 1 )
                )
                B
            )
          )
        )
      )
    )
  )
  /\
  (
    ( NTP4VCStrictOrder D )
    /\
    (
      (
        NTP4VCBeforeLast
          D
          B
          (
            NTP4VCSeqAt
              D
              ( ( # ` D ) - 1 )
          )
      )
      /\
      (
        ( NTP4VCSetEnumerates E D )
        /\
        E C_ A
      )
    )
  )
) $.

${
  $d i A B $.

  ntp4vc-unchanged-definition $a |- (
    NTP4VCUnchanged A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` A )
        )
        ->
        ( NTP4VCAt A i ) = ( NTP4VCAt B i )
      )
  ) $.
$}

${
  $d p A B $.

  ntp4vc-no-greater-definition $a |- (
    NTP4VCNoGreater A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    A. p e. Word ZZ
      (
        ( NTP4VCPerm p B )
        ->
        -. ( NTP4VCLexLT A p )
      )
  ) $.
$}

${
  $d p A B C $.

  ntp4vc-no-between-definition $a |- (
    NTP4VCNoBetween A B C
  ) <->
  (
    (
      A e. Word ZZ
      /\
      (
        B e. Word ZZ
        /\
        C e. Word ZZ
      )
    )
    /\
    A. p e. Word ZZ
      (
        ( NTP4VCPerm p C )
        ->
        -.
        (
          ( NTP4VCLexLT A p )
          /\
          ( NTP4VCLexLT p B )
        )
      )
  ) $.
$}

ntp4vc-next-contract-definition $a |- (
  NTP4VCNextContract A B C D
) <->
(
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      C e. Word ZZ
      /\
      D e. { 0 , 1 }
    )
  )
  /\
  (
    ( NTP4VCPerm C A )
    /\
    (
      (
        D = 0
        ->
        ( NTP4VCUnchanged C B )
      )
      /\
      (
        D = 0
        ->
        ( NTP4VCNoGreater C A )
      )
    )
  )
  /\
  (
    (
      D = 1
      ->
      ( NTP4VCLexLT B C )
    )
    /\
    (
      D = 1
      ->
      ( NTP4VCNoBetween B C A )
    )
  )
) $.

ntp4vc-variant-decrease-definition $a |- (
  NTP4VCVariantDecrease A B C
) <->
(
  (
    A e. NTP4VCFSet
    /\
    (
      B e. NTP4VCFSet
      /\
      C e. Word ZZ
    )
  )
  /\
  (
    0 <_ ( ( # ` A ) - ( # ` B ) )
    /\
    (
      ( # ` A ) - ( # ` ( B u. { C } ) )
    )
    <
    (
      ( # ` A ) - ( # ` B )
    )
  )
) $.

ntp4vc-success-definition $a |- (
  NTP4VCSuccess A B C D E
) <->
(
  ( NTP4VCVariantDecrease A C E )
  /\
  (
    NTP4VCLoopInv
      A
      B
      E
      ( NTP4VCSnoc D E )
      ( C u. { E } )
  )
) $.

${
  $d i p A B $.

  ntp4vc-final-definition $a |- (
    NTP4VCFinal A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    (
      ( NTP4VCAllResultPerms B A )
      /\
      ( NTP4VCStrictOrder B )
    )
    /\
    A. p e. Word ZZ
      (
        ( NTP4VCPerm p A )
        ->
        E. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < ( # ` B )
            )
            /\
            ( NTP4VCSeqAt B i ) = p
          )
      )
  ) $.
$}

${
  $d b A B C D E F G $.

  ntp4vc-loop-step-definition $a |- (
    NTP4VCLoopStep A B C D E F G
  ) <->
  A. b e. { 0 , 1 }
    (
      ( NTP4VCNextContract C F G b )
      ->
      (
        (
          b = 1
          ->
          ( NTP4VCSuccess A C D E G )
        )
        /\
        (
          b = 0
          ->
          ( NTP4VCFinal B E )
        )
      )
    ) $.
$}

${
  $d q r t u A B C D $.

  ntp4vc-loop-obligation-definition $a |- (
    NTP4VCLoopObligation A B C D
  ) <->
  A. q e. NTP4VCFSet
    A. r e. Word ( Word ZZ )
      A. t e. Word ZZ
        (
          ( # ` t ) = ( # ` D )
          ->
          (
            ( NTP4VCLoopInv A C t r q )
            ->
            (
              (
                ( # ` t ) = ( # ` C )
                /\
                ( NTP4VCPerm t C )
              )
              /\
              A. u e. Word ZZ
                (
                  ( # ` u ) = ( # ` t )
                  ->
                  (
                    NTP4VCLoopStep
                      A
                      B
                      C
                      q
                      r
                      t
                      u
                  )
                )
            )
          )
        ) $.
$}

ntp4vc-after-sort-definition $a |- (
  NTP4VCAfterSort A B C
) <->
(
  (
    ( # ` C ) = ( # ` B )
    /\
    (
      ( NTP4VCAscending C )
      /\
      ( NTP4VCPerm C B )
    )
  )
  ->
  (
    (
      NTP4VCLoopInv
        ( A ` B )
        B
        C
        ( NTP4VCSnoc (/) C )
        { C }
    )
    /\
    (
      NTP4VCLoopObligation
        ( A ` B )
        B
        B
        C
    )
  )
) $.

${
  $d s A B $.

  ntp4vc-permut-vc-definition $a |- (
    NTP4VCPermutVC A B
  ) <->
  (
    (
      B e. Word ZZ
      /\
      ( A ` B ) e. NTP4VCFSet
    )
    /\
    A. s e. Word ZZ
      ( NTP4VCAfterSort A B s )
  ) $.
$}

${
  $d b i j k p q r s t u v x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source parameter a. $)
  ntp4vc-a-word $e |- A e. Word ZZ $.

  $( The source all_permutations function and its full inclusion contract. $)
  ntp4vc-all-permutations-function
    $e |- H e. ( NTP4VCFSet ^m Word ZZ ) $.

  ntp4vc-all-permutations-contract
    $e |- A. s e. Word ZZ
      A. p e. Word ZZ
        (
          ( NTP4VCPerm p s )
          ->
          p e. ( H ` s )
        ) $.

  ntp4vc-pearl-verifythis-2021-lexicographic-permutations-1-top-permut-vc
    $a |- ( NTP4VCPermutVC H A ) $.
$}
