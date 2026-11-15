$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_nextqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_lexicographic_permutations_1_Top_nextqtvc):
  the verification condition for finding the lexicographically next
  permutation by locating a descending suffix, swapping its pivot, reversing
  the suffix, and excluding every intermediate permutation. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat and
  NTP4VCAt reproduce the exports' integer-to-natural conversion and totalized
  lookup. NTP4VCOcc, NTP4VCPerm, NTP4VCDescending, and NTP4VCLexLT directly
  encode the primary Why3 occurrence, permutation, descending-suffix, and
  strict lexicographic-order predicates.

  The Why3 to_seq operation is replaced by the same finite word: its two
  specifications give equal length and equality at every valid index, hence
  finite-word extensionality gives equality in both directions. Let-bound
  integers are substituted definitionally. The uniquely determined Boolean
  loop test and every proposition-valued conditional are represented by
  exhaustive guarded disjunctions. Expanding the remaining named predicates
  recovers every exported integer and word quantifier, bound, implication,
  swap premise, loop invariant, variant inequality, contradiction scan, and
  final no-intermediate-permutation conclusion.

  The two source theorem assumptions remain separate essential hypotheses.
  Every auxiliary $a declaration is syntax or an explicit faithful
  definition. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCOcc
  NTP4VCPerm NTP4VCDescending NTP4VCLexLT NTP4VCSwap
  NTP4VCFirstInv NTP4VCDecrement NTP4VCLast
  NTP4VCSearchInv NTP4VCSearchAdvance
  NTP4VCReverseInitial NTP4VCReverseInv NTP4VCReverseNext
  NTP4VCScan NTP4VCIsNext NTP4VCNoBetween
  NTP4VCReverseBranch NTP4VCReverseLoop
  NTP4VCSwapContinuation NTP4VCSearchStep NTP4VCSearch
  NTP4VCLoopOutcome NTP4VCFirstLoop NTP4VCNextVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B ) $.

ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-descending-syntax
  $a wff ( NTP4VCDescending A B C ) $.
ntp4vc-lex-lt-syntax
  $a wff ( NTP4VCLexLT A B ) $.
ntp4vc-swap-syntax
  $a wff ( NTP4VCSwap A B C D ) $.

ntp4vc-first-inv-syntax
  $a wff ( NTP4VCFirstInv A B ) $.
ntp4vc-decrement-syntax
  $a wff ( NTP4VCDecrement A B ) $.
ntp4vc-last-syntax
  $a wff ( NTP4VCLast A B ) $.
ntp4vc-search-inv-syntax
  $a wff ( NTP4VCSearchInv A B C ) $.
ntp4vc-search-advance-syntax
  $a wff ( NTP4VCSearchAdvance A B C ) $.

ntp4vc-reverse-initial-syntax
  $a wff ( NTP4VCReverseInitial A B C D E ) $.
ntp4vc-reverse-inv-syntax
  $a wff ( NTP4VCReverseInv A B C D E F G H ) $.
ntp4vc-reverse-next-syntax
  $a wff ( NTP4VCReverseNext A B C D E F G H ) $.
ntp4vc-scan-syntax
  $a wff ( NTP4VCScan A B C D ) $.
ntp4vc-is-next-syntax
  $a wff ( NTP4VCIsNext A B C D E F ) $.
ntp4vc-no-between-syntax
  $a wff ( NTP4VCNoBetween A B C ) $.
ntp4vc-reverse-branch-syntax
  $a wff ( NTP4VCReverseBranch A B C D E F G H ) $.
ntp4vc-reverse-loop-syntax
  $a wff ( NTP4VCReverseLoop A B C D E ) $.
ntp4vc-swap-continuation-syntax
  $a wff ( NTP4VCSwapContinuation A B C D ) $.

ntp4vc-search-step-syntax
  $a wff ( NTP4VCSearchStep A B C D ) $.
ntp4vc-search-syntax
  $a wff ( NTP4VCSearch A B C ) $.
ntp4vc-loop-outcome-syntax
  $a wff ( NTP4VCLoopOutcome A B C ) $.
ntp4vc-first-loop-syntax
  $a wff ( NTP4VCFirstLoop A B ) $.
ntp4vc-next-vc-syntax
  $a wff ( NTP4VCNextVC A B ) $.

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
  $d i j A B C $.

  ntp4vc-descending-definition $a |- (
    NTP4VCDescending A B C
  ) <->
  (
    (
      A e. Word ZZ
      /\
      (
        0 <_ B
        /\
        (
          B <_ C
          /\
          C <_ ( # ` A )
        )
      )
    )
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            B <_ i
            /\
            (
              i <_ j
              /\
              j < C
            )
          )
          ->
          ( NTP4VCAt A j ) <_ ( NTP4VCAt A i )
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
        0 < ( # ` B )
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
  $d k A B C D $.

  ntp4vc-swap-definition $a |- (
    NTP4VCSwap A B C D
  ) <->
  (
    (
      ( NTP4VCAt B C ) = ( NTP4VCAt A D )
      /\
      ( NTP4VCAt B D ) = ( NTP4VCAt A C )
    )
    /\
    A. k e. ZZ
      (
        (
          0 <_ k
          /\
          k < ( # ` B )
        )
        ->
        (
          k =/= C
          ->
          (
            k =/= D
            ->
            ( NTP4VCAt B k ) = ( NTP4VCAt A k )
          )
        )
      )
  ) $.
$}

ntp4vc-first-inv-definition $a |- (
  NTP4VCFirstInv A B
) <->
(
  (
    ( -u 1 ) <_ B
    /\
    B < ( # ` A )
  )
  /\
  (
    (
      B = ( -u 1 )
      /\
      ( # ` A ) = 0
    )
    \/
    (
      0 <_ B
      /\
      ( NTP4VCDescending A B ( # ` A ) )
    )
  )
) $.

ntp4vc-decrement-definition $a |- (
  NTP4VCDecrement A B
) <->
(
  (
    0 <_ B
    /\
    ( B - 1 ) < B
  )
  /\
  ( NTP4VCFirstInv A ( B - 1 ) )
) $.

${
  $d p A B $.

  ntp4vc-last-definition $a |- (
    NTP4VCLast A B
  ) <->
  (
    ( NTP4VCPerm A B )
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
  $d k A B C $.

  ntp4vc-search-inv-definition $a |- (
    NTP4VCSearchInv A B C
  ) <->
  (
    (
      B <_ C
      /\
      C < ( # ` A )
    )
    /\
    A. k e. ZZ
      (
        (
          C < k
          /\
          k < ( # ` A )
        )
        ->
        ( NTP4VCAt A k ) <_ ( NTP4VCAt A ( B - 1 ) )
      )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-search-advance-definition $a |- (
    NTP4VCSearchAdvance A B C
  ) <->
  (
    (
      0 <_ C
      /\
      ( C - 1 ) < C
    )
    /\
    (
      (
        B <_ ( C - 1 )
        /\
        ( C - 1 ) < ( # ` A )
      )
      /\
      A. k e. ZZ
        (
          (
            ( C - 1 ) < k
            /\
            k < ( # ` A )
          )
          ->
          ( NTP4VCAt A k ) <_ ( NTP4VCAt A ( B - 1 ) )
        )
    )
  ) $.
$}

${
  $d k A B C D E $.

  ntp4vc-reverse-initial-definition $a |- (
    NTP4VCReverseInitial A B C D E
  ) <->
  (
    (
      (
        ( D - 1 ) < D
        /\
        (
          ( D - 1 ) < ( ( # ` A ) - 1 )
          /\
          ( ( # ` A ) - 1 ) < ( # ` A )
        )
      )
      /\
      ( NTP4VCPerm C B )
    )
    /\
    (
      A. k e. ZZ
        (
          (
            0 <_ k
            /\
            k < ( D - 1 )
          )
          ->
          ( NTP4VCAt C k ) = ( NTP4VCAt A k )
        )
      /\
      (
        ( NTP4VCAt C ( D - 1 ) ) = ( NTP4VCAt A E )
        /\
        (
          (
            D - ( D - 1 )
          )
          =
          (
            ( # ` A ) - ( ( # ` A ) - 1 )
          )
          /\
          A. k e. ZZ
            (
              (
                0 < k
                /\
                k < ( D - ( D - 1 ) )
              )
              ->
              (
                (
                  NTP4VCAt C ( ( D - 1 ) + k )
                )
                =
                (
                  NTP4VCAt C ( ( # ` A ) - k )
                )
                /\
                (
                  NTP4VCAt C ( ( # ` A ) - k )
                )
                =
                (
                  NTP4VCAt C ( ( D - 1 ) + k )
                )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d k A B C D E F G H $.

  ntp4vc-reverse-inv-definition $a |- (
    NTP4VCReverseInv A B C D E F G H
  ) <->
  (
    (
      (
        ( D - 1 ) < F
        /\
        (
          ( D - 1 ) < G
          /\
          G < ( # ` A )
        )
      )
      /\
      ( NTP4VCPerm H B )
    )
    /\
    (
      A. k e. ZZ
        (
          (
            0 <_ k
            /\
            k < ( D - 1 )
          )
          ->
          ( NTP4VCAt H k ) = ( NTP4VCAt A k )
        )
      /\
      (
        ( NTP4VCAt H ( D - 1 ) ) = ( NTP4VCAt A E )
        /\
        (
          ( F - ( D - 1 ) ) = ( ( # ` A ) - G )
          /\
          (
            A. k e. ZZ
              (
                (
                  F <_ k
                  /\
                  k <_ G
                )
                ->
                ( NTP4VCAt H k ) = ( NTP4VCAt C k )
              )
            /\
            A. k e. ZZ
              (
                (
                  0 < k
                  /\
                  k < ( F - ( D - 1 ) )
                )
                ->
                (
                  (
                    NTP4VCAt H ( ( D - 1 ) + k )
                  )
                  =
                  (
                    NTP4VCAt C ( ( # ` A ) - k )
                  )
                  /\
                  (
                    NTP4VCAt H ( ( # ` A ) - k )
                  )
                  =
                  (
                    NTP4VCAt C ( ( D - 1 ) + k )
                  )
                )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d k A B C D E F G H $.

  ntp4vc-reverse-next-definition $a |- (
    NTP4VCReverseNext A B C D E F G H
  ) <->
  (
    (
      0 <_ ( G - F )
      /\
      (
        ( ( G - 1 ) - ( F + 1 ) )
        <
        ( G - F )
      )
    )
    /\
    (
      (
        ( D - 1 ) < ( F + 1 )
        /\
        (
          ( D - 1 ) < ( G - 1 )
          /\
          ( G - 1 ) < ( # ` A )
        )
      )
      /\
      (
        ( NTP4VCPerm H B )
        /\
        (
          A. k e. ZZ
            (
              (
                0 <_ k
                /\
                k < ( D - 1 )
              )
              ->
              ( NTP4VCAt H k ) = ( NTP4VCAt A k )
            )
          /\
          (
            ( NTP4VCAt H ( D - 1 ) ) = ( NTP4VCAt A E )
            /\
            (
              (
                ( F + 1 ) - ( D - 1 )
              )
              =
              (
                ( # ` A ) - ( G - 1 )
              )
              /\
              (
                A. k e. ZZ
                  (
                    (
                      ( F + 1 ) <_ k
                      /\
                      k <_ ( G - 1 )
                    )
                    ->
                    ( NTP4VCAt H k ) = ( NTP4VCAt C k )
                  )
                /\
                A. k e. ZZ
                  (
                    (
                      0 < k
                      /\
                      k < ( ( F + 1 ) - ( D - 1 ) )
                    )
                    ->
                    (
                      (
                        NTP4VCAt H ( ( D - 1 ) + k )
                      )
                      =
                      (
                        NTP4VCAt C ( ( # ` A ) - k )
                      )
                      /\
                      (
                        NTP4VCAt H ( ( # ` A ) - k )
                      )
                      =
                      (
                        NTP4VCAt C ( ( D - 1 ) + k )
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
$}

${
  $d k l A B C D $.

  ntp4vc-scan-definition $a |- (
    NTP4VCScan A B C D
  ) <->
  (
    (
      (
        ( C + 1 ) <_ ( ( D - 1 ) + 1 )
      )
      ->
      (
        A. k e. ZZ
          (
            (
              ( C + 1 ) <_ k
              /\
              k < ( C + 1 )
            )
            ->
            ( NTP4VCAt A k ) = ( NTP4VCAt B k )
          )
        /\
        (
          A. l e. ZZ
            (
              (
                (
                  ( C + 1 ) <_ l
                  /\
                  l <_ ( D - 1 )
                )
                /\
                A. k e. ZZ
                  (
                    (
                      ( C + 1 ) <_ k
                      /\
                      k < l
                    )
                    ->
                    ( NTP4VCAt A k ) = ( NTP4VCAt B k )
                  )
              )
              ->
              (
                ( NTP4VCAt A l ) = ( NTP4VCAt B l )
                /\
                A. k e. ZZ
                  (
                    (
                      ( C + 1 ) <_ k
                      /\
                      k < ( l + 1 )
                    )
                    ->
                    ( NTP4VCAt A k ) = ( NTP4VCAt B k )
                  )
              )
            )
          /\
          -. A. k e. ZZ
            (
              (
                ( C + 1 ) <_ k
                /\
                k < ( ( D - 1 ) + 1 )
              )
              ->
              ( NTP4VCAt A k ) = ( NTP4VCAt B k )
            )
        )
      )
    )
    /\
    -. ( ( D - 1 ) + 1 ) < ( C + 1 )
  ) $.
$}

${
  $d p A B C D E F $.

  ntp4vc-is-next-definition $a |- (
    NTP4VCIsNext A B C D E F
  ) <->
  A. p e. Word ZZ
    (
      (
        ( NTP4VCPerm p B )
        /\
        (
          ( NTP4VCLexLT A p )
          /\
          ( NTP4VCLexLT p C )
        )
      )
      ->
      (
        (
          ( NTP4VCAt p D ) = E
          /\
          ( NTP4VCScan p A D ( # ` A ) )
        )
        \/
        (
          ( NTP4VCAt p D ) =/= E
          /\
          (
            ( NTP4VCAt p D ) = F
            /\
            ( NTP4VCScan p C D ( # ` A ) )
          )
        )
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
      A. p e. Word ZZ
        -.
        (
          ( NTP4VCPerm p B )
          /\
          (
            ( NTP4VCLexLT A p )
            /\
            ( NTP4VCLexLT p C )
          )
        )
    )
    ->
    (
      ( NTP4VCPerm C B )
      /\
      (
        ( NTP4VCLexLT A C )
        /\
        A. p e. Word ZZ
          (
            ( NTP4VCPerm p B )
            ->
            -.
            (
              ( NTP4VCLexLT A p )
              /\
              ( NTP4VCLexLT p C )
            )
          )
      )
    )
  ) $.
$}

${
  $d z A B C D E F G H $.

  ntp4vc-reverse-branch-definition $a |- (
    NTP4VCReverseBranch A B C D E F G H
  ) <->
  (
    (
      F < G
      /\
      (
        (
          0 <_ F
          /\
          F < ( # ` H )
        )
        /\
        (
          0 <_ G
          /\
          G < ( # ` H )
        )
        /\
        A. z e. Word ZZ
          (
            ( # ` z ) = ( # ` H )
            ->
            (
              (
                ( NTP4VCSwap H z F G )
                /\
                ( NTP4VCPerm z H )
              )
              ->
              (
                NTP4VCReverseNext
                  A B C D E F G z
              )
            )
          )
      )
    )
    \/
    (
      -. F < G
      /\
      (
        (
          NTP4VCIsNext
            A B H ( D - 1 )
            ( NTP4VCAt A ( D - 1 ) )
            ( NTP4VCAt A E )
        )
        /\
        ( NTP4VCNoBetween A B H )
      )
    )
  ) $.
$}

${
  $d y i1 j1 A B C D E $.

  ntp4vc-reverse-loop-definition $a |- (
    NTP4VCReverseLoop A B C D E
  ) <->
  A. j1 e. ZZ
    A. i1 e. ZZ
      A. y e. Word ZZ
        (
          ( # ` y ) = ( # ` C )
          ->
          (
            ( NTP4VCReverseInv A B C D E i1 j1 y )
            ->
            (
              NTP4VCReverseBranch
                A B C D E i1 j1 y
            )
          )
        ) $.
$}

${
  $d x A B C D $.

  ntp4vc-swap-continuation-definition $a |- (
    NTP4VCSwapContinuation A B C D
  ) <->
  A. x e. Word ZZ
    (
      ( # ` x ) = ( # ` A )
      ->
      (
        (
          ( NTP4VCSwap A x ( C - 1 ) D )
          /\
          ( NTP4VCPerm x A )
        )
        ->
        (
          ( NTP4VCReverseInitial A B x C D )
          /\
          ( NTP4VCReverseLoop A B x C D )
        )
      )
    ) $.
$}

ntp4vc-search-step-definition $a |- (
  NTP4VCSearchStep A B C D
) <->
(
  (
    (
      0 <_ ( C - 1 )
      /\
      ( C - 1 ) < ( # ` A )
    )
    /\
    (
      0 <_ D
      /\
      D < ( # ` A )
    )
  )
  /\
  (
    (
      ( NTP4VCAt A D ) <_ ( NTP4VCAt A ( C - 1 ) )
      /\
      ( NTP4VCSearchAdvance A C D )
    )
    \/
    (
      -. ( NTP4VCAt A D ) <_ ( NTP4VCAt A ( C - 1 ) )
      /\
      (
        (
          0 <_ D
          /\
          D < ( # ` A )
        )
        /\
        ( NTP4VCSwapContinuation A B C D )
      )
    )
  )
) $.

${
  $d j k A B C $.

  ntp4vc-search-definition $a |- (
    NTP4VCSearch A B C
  ) <->
  (
    (
      0 <_ ( C - 1 )
      /\
      ( C - 1 ) < ( # ` A )
    )
    /\
    (
      (
        (
          C <_ ( ( # ` A ) - 1 )
          /\
          ( ( # ` A ) - 1 ) < ( # ` A )
        )
        /\
        A. k e. ZZ
          (
            (
              ( ( # ` A ) - 1 ) < k
              /\
              k < ( # ` A )
            )
            ->
            ( NTP4VCAt A k ) <_ ( NTP4VCAt A ( C - 1 ) )
          )
      )
      /\
      A. j e. ZZ
        (
          ( NTP4VCSearchInv A C j )
          ->
          ( NTP4VCSearchStep A B C j )
        )
    )
  ) $.
$}

ntp4vc-loop-outcome-definition $a |- (
  NTP4VCLoopOutcome A B C
) <->
(
  (
    (
      0 < C
      /\
      ( NTP4VCAt A C ) <_ ( NTP4VCAt A ( C - 1 ) )
    )
    /\
    ( NTP4VCDecrement A C )
  )
  \/
  (
    -.
    (
      0 < C
      /\
      ( NTP4VCAt A C ) <_ ( NTP4VCAt A ( C - 1 ) )
    )
    /\
    (
      (
        C <_ 0
        /\
        ( NTP4VCLast A B )
      )
      \/
      (
        -. C <_ 0
        /\
        ( NTP4VCSearch A B C )
      )
    )
  )
) $.

${
  $d i A B $.

  ntp4vc-first-loop-definition $a |- (
    NTP4VCFirstLoop A B
  ) <->
  A. i e. ZZ
    (
      ( NTP4VCFirstInv A i )
      ->
      (
        (
          0 < i
          ->
          (
            (
              0 <_ i
              /\
              i < ( # ` A )
            )
            /\
            (
              0 <_ ( i - 1 )
              /\
              ( i - 1 ) < ( # ` A )
            )
          )
        )
        /\
        ( NTP4VCLoopOutcome A B i )
      )
    ) $.
$}

ntp4vc-next-vc-definition $a |- (
  NTP4VCNextVC A B
) <->
(
  (
    NTP4VCFirstInv
      A
      ( ( # ` A ) - 1 )
  )
  /\
  ( NTP4VCFirstLoop A B )
) $.

${
  $d x y z i i1 j j1 k l p v
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source theorem parameters a and a0, followed by fact0 and fact1. $)
  ntp4vc-a-word $e |- A e. Word ZZ $.
  ntp4vc-a0-word $e |- B e. Word ZZ $.

  ntp4vc-fact0 $e |- ( # ` A ) = ( # ` B ) $.
  ntp4vc-fact1 $e |- ( NTP4VCPerm A B ) $.

  ntp4vc-pearl-verifythis-2021-lexicographic-permutations-1-top-next-vc
    $a |- ( NTP4VCNextVC A B ) $.
$}
