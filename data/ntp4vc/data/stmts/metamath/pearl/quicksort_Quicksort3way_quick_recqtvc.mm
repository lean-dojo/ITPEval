$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/quicksort_Quicksort3way_quick_recqtvc: the three-way quicksort
  recursion verification condition states initialization and preservation of
  the less-than, equal-to, and greater-than pivot regions, variant decrease,
  and the two recursive sorted-permutation obligations. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat,
  NTP4VCAt, NTP4VCSet, and NTP4VCSlice reproduce the source Int.toNat,
  totalized list lookup with default zero, List.set, and drop-then-take slice.

  NTP4VCPerm compares the occurrence count of every integer and is
  bidirectionally equivalent to List.Perm on finite integer words.
  NTP4VCPermutSub is exactly the source permut_sub' predicate, and
  NTP4VCSortedSub is the source integer-indexed sorted_sub1 predicate.
  NTP4VCExchange is the source arrayExchange equation, retaining its
  direction and nested List.set order. NTP4VCPartition directly encodes the
  source qs_partition definition.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers every source
  bound, quantifier, implication, loop invariant, swap continuation,
  recursive continuation, and conclusion. Let-bound values are replaced by
  direct substitution, and proposition-valued conditionals are represented
  by equivalent exhaustive guarded disjunctions. Every integer and integer
  list quantifier retains its full source domain. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice
  NTP4VCAt NTP4VCSet
  NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub
  NTP4VCExchange NTP4VCPartition
  NTP4VCInitial NTP4VCInvariant
  NTP4VCLessResult NTP4VCLessBranch
  NTP4VCGreaterResult NTP4VCGreaterBranch
  NTP4VCEqualResult NTP4VCFinish
  NTP4VCStep NTP4VCLoop NTP4VCBase NTP4VCQuickRecVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B ) $.
ntp4vc-permut-sub-syntax
  $a wff ( NTP4VCPermutSub A B C D ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C ) $.
ntp4vc-exchange-syntax
  $a wff ( NTP4VCExchange A B C D ) $.
ntp4vc-partition-syntax
  $a wff ( NTP4VCPartition A B C D E F G ) $.

ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F G H ) $.
ntp4vc-less-result-syntax
  $a wff ( NTP4VCLessResult A B C D E F G H ) $.
ntp4vc-less-branch-syntax
  $a wff ( NTP4VCLessBranch A B C D E F G H ) $.
ntp4vc-greater-result-syntax
  $a wff ( NTP4VCGreaterResult A B C D E F G H ) $.
ntp4vc-greater-branch-syntax
  $a wff ( NTP4VCGreaterBranch A B C D E F G H ) $.
ntp4vc-equal-result-syntax
  $a wff ( NTP4VCEqualResult A B C D E F G H ) $.
ntp4vc-finish-syntax
  $a wff ( NTP4VCFinish A B C D E F G H ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G H ) $.
ntp4vc-loop-syntax
  $a wff ( NTP4VCLoop A B C D ) $.
ntp4vc-base-syntax
  $a wff ( NTP4VCBase A B C ) $.
ntp4vc-quick-rec-vc-syntax
  $a wff ( NTP4VCQuickRecVC A B C ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-nat-sub-definition $a |- (
  NTP4VCNatSub A B
) = if (
  B <_ A ,
  ( A - B ) ,
  0
) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if (
  A <_ B ,
  A ,
  B
) $.

ntp4vc-slice-start-definition $a |- (
  NTP4VCSliceStart A B
) = (
  NTP4VCMin ( NTP4VCToNat B ) ( # ` A )
) $.

ntp4vc-slice-len-definition $a |- (
  NTP4VCSliceLen A B C
) = (
  NTP4VCMin
    ( NTP4VCNatSub ( NTP4VCToNat C ) ( NTP4VCToNat B ) )
    ( ( # ` A ) - ( NTP4VCSliceStart A B ) )
) $.

${
  $d k A B C $.

  ntp4vc-slice-definition $a |- (
    NTP4VCSlice A B C
  ) = (
    k e. ( 0 ..^ ( NTP4VCSliceLen A B C ) ) |->
      ( A ` ( ( NTP4VCSliceStart A B ) + k ) )
  ) $.
$}

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

${
  $d k v A B $.

  ntp4vc-perm-definition $a |- (
    ( NTP4VCPerm A B )
    <->
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
            (
              # `
              { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
            )
            =
            (
              # `
              { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
            )
          )
      )
    )
  ) $.
$}

ntp4vc-permut-sub-definition $a |- (
  ( NTP4VCPermutSub A B C D )
  <->
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
      (
        ( NTP4VCSlice A 0 C ) = ( NTP4VCSlice B 0 C )
        /\
        (
          ( NTP4VCSlice A D ( # ` A ) )
          =
          ( NTP4VCSlice B D ( # ` B ) )
          /\
          (
            NTP4VCPerm
              ( NTP4VCSlice A C D )
              ( NTP4VCSlice B C D )
          )
        )
      )
    )
  )
) $.

${
  $d i j A B C $.

  ntp4vc-sorted-sub-definition $a |- (
    ( NTP4VCSortedSub A B C )
    <->
    (
      A e. Word ZZ
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
            ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
          )
    )
  ) $.
$}

ntp4vc-exchange-definition $a |- (
  ( NTP4VCExchange A B C D )
  <->
  B = (
    NTP4VCSet
      ( NTP4VCSet A C ( NTP4VCAt A D ) )
      D
      ( NTP4VCAt A C )
  )
) $.

${
  $d j A B C D E F G $.

  ntp4vc-partition-definition $a |- (
    ( NTP4VCPartition A B C D E F G )
    <->
    (
      ( NTP4VCPermutSub A B C F )
      /\
      (
        A. j e. ZZ
          (
            (
              C <_ j
              /\
              j < D
            )
            ->
            ( NTP4VCAt B j ) < G
          )
        /\
        (
          A. j e. ZZ
            (
              (
                D <_ j
                /\
                j < E
              )
              ->
              ( NTP4VCAt B j ) = G
            )
          /\
          A. j e. ZZ
            (
              (
                E <_ j
                /\
                j < F
              )
              ->
              G < ( NTP4VCAt B j )
            )
        )
      )
    )
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-initial-definition $a |- (
    ( NTP4VCInitial A B C )
    <->
    (
      (
        A <_ A
        /\
        (
          A < ( A + 1 )
          /\
          (
            ( A + 1 ) <_ B
            /\
            B <_ B
          )
        )
      )
      /\
      (
        A. j e. ZZ
          (
            (
              A <_ j
              /\
              j < A
            )
            ->
            ( NTP4VCAt C j ) < ( NTP4VCAt C A )
          )
        /\
        (
          A. j e. ZZ
            (
              (
                A <_ j
                /\
                j < ( A + 1 )
              )
              ->
              ( NTP4VCAt C j ) = ( NTP4VCAt C A )
            )
          /\
          (
            A. j e. ZZ
              (
                (
                  B <_ j
                  /\
                  j < B
                )
                ->
                ( NTP4VCAt C A ) < ( NTP4VCAt C j )
              )
            /\
            ( NTP4VCPermutSub C C A B )
          )
        )
      )
    )
  ) $.
$}

${
  $d j A B C D E F G H $.

  $( A=a1, B=original a, C=l, D=ml, E=i, F=mr, G=r, H=v. $)
  ntp4vc-invariant-definition $a |- (
    ( NTP4VCInvariant A B C D E F G H )
    <->
    (
      (
        ( # ` A ) = ( # ` B )
        /\
        (
          C <_ D
          /\
          (
            D < E
            /\
            (
              E <_ F
              /\
              F <_ G
            )
          )
        )
      )
      /\
      (
        A. j e. ZZ
          (
            (
              C <_ j
              /\
              j < D
            )
            ->
            ( NTP4VCAt A j ) < H
          )
        /\
        (
          A. j e. ZZ
            (
              (
                D <_ j
                /\
                j < E
              )
              ->
              ( NTP4VCAt A j ) = H
            )
          /\
          (
            A. j e. ZZ
              (
                (
                  F <_ j
                  /\
                  j < G
                )
                ->
                H < ( NTP4VCAt A j )
              )
            /\
            ( NTP4VCPermutSub B A C G )
          )
        )
      )
    )
  ) $.
$}

${
  $d j A B C D E F G H $.

  $( A=a2, B=original a, C=l, D=ml, E=i, F=mr, G=r, H=v. $)
  ntp4vc-less-result-definition $a |- (
    ( NTP4VCLessResult A B C D E F G H )
    <->
    (
      (
        0 <_ ( F - E )
        /\
        ( F - ( E + 1 ) ) < ( F - E )
      )
      /\
      (
        (
          C <_ ( D + 1 )
          /\
          (
            ( D + 1 ) < ( E + 1 )
            /\
            (
              ( E + 1 ) <_ F
              /\
              F <_ G
            )
          )
        )
        /\
        (
          A. j e. ZZ
            (
              (
                C <_ j
                /\
                j < ( D + 1 )
              )
              ->
              ( NTP4VCAt A j ) < H
            )
          /\
          (
            A. j e. ZZ
              (
                (
                  ( D + 1 ) <_ j
                  /\
                  j < ( E + 1 )
                )
                ->
                ( NTP4VCAt A j ) = H
              )
            /\
            (
              A. j e. ZZ
                (
                  (
                    F <_ j
                    /\
                    j < G
                  )
                  ->
                  H < ( NTP4VCAt A j )
                )
              /\
              ( NTP4VCPermutSub B A C G )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G H $.

  $( A=a1, B=original a, C=l, D=ml, E=i, F=mr, G=r, H=v. $)
  ntp4vc-less-branch-definition $a |- (
    ( NTP4VCLessBranch A B C D E F G H )
    <->
    (
      (
        (
          0 <_ D
          /\
          D < ( # ` A )
        )
        /\
        (
          0 <_ E
          /\
          E < ( # ` A )
        )
      )
      /\
      A. x e. Word ZZ
        (
          ( # ` x ) = ( # ` A )
          ->
          (
            ( NTP4VCExchange A x D E )
            ->
            ( NTP4VCLessResult x B C D E F G H )
          )
        )
    )
  ) $.
$}

${
  $d j A B C D E F G H $.

  $( A=a2, B=original a, C=l, D=ml, E=i, F=mr, G=r, H=v. $)
  ntp4vc-greater-result-definition $a |- (
    ( NTP4VCGreaterResult A B C D E F G H )
    <->
    (
      (
        0 <_ ( F - E )
        /\
        ( ( F - 1 ) - E ) < ( F - E )
      )
      /\
      (
        (
          C <_ D
          /\
          (
            D < E
            /\
            (
              E <_ ( F - 1 )
              /\
              ( F - 1 ) <_ G
            )
          )
        )
        /\
        (
          A. j e. ZZ
            (
              (
                C <_ j
                /\
                j < D
              )
              ->
              ( NTP4VCAt A j ) < H
            )
          /\
          (
            A. j e. ZZ
              (
                (
                  D <_ j
                  /\
                  j < E
                )
                ->
                ( NTP4VCAt A j ) = H
              )
            /\
            (
              A. j e. ZZ
                (
                  (
                    ( F - 1 ) <_ j
                    /\
                    j < G
                  )
                  ->
                  H < ( NTP4VCAt A j )
                )
              /\
              ( NTP4VCPermutSub B A C G )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G H $.

  $( A=a1, B=original a, C=l, D=ml, E=i, F=mr, G=r, H=v. $)
  ntp4vc-greater-branch-definition $a |- (
    ( NTP4VCGreaterBranch A B C D E F G H )
    <->
    (
      (
        (
          0 <_ E
          /\
          E < ( # ` A )
        )
        /\
        (
          0 <_ ( F - 1 )
          /\
          ( F - 1 ) < ( # ` A )
        )
      )
      /\
      A. x e. Word ZZ
        (
          ( # ` x ) = ( # ` A )
          ->
          (
            ( NTP4VCExchange A x E ( F - 1 ) )
            ->
            ( NTP4VCGreaterResult x B C D E F G H )
          )
        )
    )
  ) $.
$}

${
  $d j A B C D E F G H $.

  $( A=a1, B=original a, C=l, D=ml, E=i, F=mr, G=r, H=v. $)
  ntp4vc-equal-result-definition $a |- (
    ( NTP4VCEqualResult A B C D E F G H )
    <->
    (
      (
        0 <_ ( F - E )
        /\
        ( F - ( E + 1 ) ) < ( F - E )
      )
      /\
      (
        (
          C <_ D
          /\
          (
            D < ( E + 1 )
            /\
            (
              ( E + 1 ) <_ F
              /\
              F <_ G
            )
          )
        )
        /\
        (
          A. j e. ZZ
            (
              (
                C <_ j
                /\
                j < D
              )
              ->
              ( NTP4VCAt A j ) < H
            )
          /\
          (
            A. j e. ZZ
              (
                (
                  D <_ j
                  /\
                  j < ( E + 1 )
                )
                ->
                ( NTP4VCAt A j ) = H
              )
            /\
            (
              A. j e. ZZ
                (
                  (
                    F <_ j
                    /\
                    j < G
                  )
                  ->
                  H < ( NTP4VCAt A j )
                )
              /\
              ( NTP4VCPermutSub B A C G )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d x y A B C D E F G H $.

  $( A=a1, B=original a, C=l, D=ml, E=i, F=mr, G=r, H=v. $)
  ntp4vc-finish-definition $a |- (
    ( NTP4VCFinish A B C D E F G H )
    <->
    (
      (
        (
          0 <_ ( G - C )
          /\
          ( D - C ) < ( G - C )
        )
        /\
        (
          0 <_ C
          /\
          (
            C <_ D
            /\
            D <_ ( # ` A )
          )
        )
      )
      /\
      A. x e. Word ZZ
        (
          ( # ` x ) = ( # ` A )
          ->
          (
            (
              ( NTP4VCSortedSub x C D )
              /\
              ( NTP4VCPermutSub A x C D )
            )
            ->
            (
              (
                (
                  0 <_ ( G - C )
                  /\
                  ( G - F ) < ( G - C )
                )
                /\
                (
                  0 <_ F
                  /\
                  (
                    F <_ G
                    /\
                    G <_ ( # ` x )
                  )
                )
              )
              /\
              A. y e. Word ZZ
                (
                  ( # ` y ) = ( # ` x )
                  ->
                  (
                    (
                      ( NTP4VCSortedSub y F G )
                      /\
                      ( NTP4VCPermutSub x y F G )
                    )
                    ->
                    (
                      ( NTP4VCSortedSub y C G )
                      /\
                      ( NTP4VCPermutSub B y C G )
                    )
                  )
                )
            )
          )
        )
    )
  ) $.
$}

ntp4vc-step-definition $a |- (
  ( NTP4VCStep A B C D E F G H )
  <->
  (
    (
      E < F
      /\
      (
        (
          0 <_ E
          /\
          E < ( # ` A )
        )
        /\
        (
          (
            ( NTP4VCAt A E ) < H
            /\
            ( NTP4VCLessBranch A B C D E F G H )
          )
          \/
          (
            -. ( NTP4VCAt A E ) < H
            /\
            (
              (
                H < ( NTP4VCAt A E )
                /\
                ( NTP4VCGreaterBranch A B C D E F G H )
              )
              \/
              (
                -. H < ( NTP4VCAt A E )
                /\
                ( NTP4VCEqualResult A B C D E F G H )
              )
            )
          )
        )
      )
    )
    \/
    (
      -. E < F
      /\
      ( NTP4VCFinish A B C D E F G H )
    )
  )
) $.

${
  $d i m n x A B C D $.

  $( A=l, B=r, C=original a, D=pivot value. $)
  ntp4vc-loop-definition $a |- (
    ( NTP4VCLoop A B C D )
    <->
    A. i e. ZZ
      A. n e. ZZ
        A. m e. ZZ
          A. x e. Word ZZ
            (
              ( # ` x ) = ( # ` C )
              ->
              (
                ( NTP4VCInvariant x C A m i n B D )
                ->
                ( NTP4VCStep x C A m i n B D )
              )
            )
  ) $.
$}

ntp4vc-base-definition $a |- (
  ( NTP4VCBase A B C )
  <->
  (
    ( NTP4VCSortedSub C A B )
    /\
    ( NTP4VCPermutSub C C A B )
  )
) $.

ntp4vc-quick-rec-vc-definition $a |- (
  ( NTP4VCQuickRecVC A B C )
  <->
  (
    (
      ( A + 1 ) < B
      /\
      (
        (
          0 <_ A
          /\
          A < ( # ` C )
        )
        /\
        (
          ( NTP4VCInitial A B C )
          /\
          ( NTP4VCLoop A B C ( NTP4VCAt C A ) )
        )
      )
    )
    \/
    (
      -. ( A + 1 ) < B
      /\
      ( NTP4VCBase A B C )
    )
  )
) $.

${
  $( Source theorem parameters A=l, B=r, and C=a. $)

  ntp4vc-l-integer $e |- A e. ZZ $.
  ntp4vc-r-integer $e |- B e. ZZ $.
  ntp4vc-a-list $e |- C e. Word ZZ $.

  ntp4vc-fact0 $e |- 0 <_ A $.
  ntp4vc-fact1 $e |- A <_ B $.
  ntp4vc-fact2 $e |- B <_ ( # ` C ) $.

  ntp4vc-pearl-quicksort3way-quick-rec-vc $a |- (
    NTP4VCQuickRecVC A B C
  ) $.
$}
