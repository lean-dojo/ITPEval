$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/algo64_Algo64_quicksortqtvc: the quicksort verification condition
  states the recursive sorting obligations for the two subranges produced by
  a partition around the integer pivot 42, preserving the original segment's
  multiset and establishing sortedness. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat is the
  source conversion from integers to naturals, NTP4VCAt is the source
  totalized list lookup with integer default 0, and NTP4VCSlice is the source
  drop-then-take slice.

  NTP4VCPerm compares the occurrence count of every integer in two words.
  For finite integer words this is equivalent in both directions to the
  source List.Perm relation. NTP4VCPermutSub is the source permut_sub':
  equal lengths and equal prefix and suffix slices, with a permutation of the
  selected middle slice. NTP4VCSortedSub is the source sorted_sub1 over all
  integer indices, using the totalized lookup.

  NTP4VCPartition directly expands the shared qs_partition definition. Its
  use in the main assertion is definitionally equivalent to the five
  partition conjuncts displayed in the ground truths. The proposition-valued
  source if is represented by the equivalent guarded disjunction. Splitting
  the theorem's typed parameters and three assumptions into scoped essential
  hypotheses is bidirectionally equivalent to the source curried theorem.
  Every integer and word quantifier retains its full source domain. The final
  declaration is Metamath's native unproved statement encoding.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice NTP4VCAt
  NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub NTP4VCPartition
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B ) $.
ntp4vc-permut-sub-syntax
  $a wff ( NTP4VCPermutSub A B C D ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C ) $.
ntp4vc-partition-syntax
  $a wff ( NTP4VCPartition A B C D E F G ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-nat-sub-definition $a |- (
  NTP4VCNatSub A B
) = if ( B <_ A , ( A - B ) , 0 ) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if ( A <_ B , A , B ) $.

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
      (
        B e. ZZ
        /\
        (
          C e. ZZ
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
      )
    )
  ) $.
$}

${
  $d k A B C D E F G $.

  ntp4vc-partition-definition $a |- (
    ( NTP4VCPartition A B C D E F G )
    <->
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        (
          C e. ZZ
          /\
          (
            D e. ZZ
            /\
            (
              E e. ZZ
              /\
              (
                F e. ZZ
                /\
                G e. ZZ
              )
            )
          )
        )
        /\
        (
          ( NTP4VCPermutSub A B C ( D + 1 ) )
          /\
          (
            A. k e. ZZ
              (
                ( C <_ k /\ k <_ F )
                ->
                ( NTP4VCAt B k ) <_ G
              )
            /\
            (
              A. k e. ZZ
                (
                  ( F < k /\ k < E )
                  ->
                  ( NTP4VCAt B k ) = G
                )
              /\
              A. k e. ZZ
                (
                  ( E <_ k /\ k <_ D )
                  ->
                  G <_ ( NTP4VCAt B k )
                )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d i j r x y z A B C $.

  $( Source parameters: A=m, B=n, and C=a. $)

  ntp4vc-m-integer $e |- A e. ZZ $.
  ntp4vc-n-integer $e |- B e. ZZ $.
  ntp4vc-a-list $e |- C e. Word ZZ $.

  ntp4vc-m-nonnegative $e |- 0 <_ A $.
  ntp4vc-m-le-n $e |- A <_ B $.
  ntp4vc-n-in-bounds $e |- B < ( # ` C ) $.

  ntp4vc-pearl-algo64-quicksort-vc $a |- (
    (
      A < B
      /\
      (
        (
          0 <_ A
          /\
          (
            A < B
            /\
            B < ( # ` C )
          )
        )
        /\
        A. j e. ZZ
          A. i e. ZZ
            A. x e. Word ZZ
              (
                ( # ` x ) = ( # ` C )
                ->
                (
                  (
                    (
                      A <_ j
                      /\
                      (
                        j < i
                        /\
                        i <_ B
                      )
                    )
                    /\
                    (
                      NTP4VCPartition
                        C x A B i j ; 4 2
                    )
                  )
                  ->
                  (
                    (
                      (
                        0 <_ ( B - A )
                        /\
                        ( j - A ) < ( B - A )
                      )
                      /\
                      (
                        0 <_ A
                        /\
                        (
                          A <_ j
                          /\
                          j < ( # ` x )
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
                            (
                              NTP4VCPermutSub
                                x y A ( j + 1 )
                            )
                            /\
                            (
                              NTP4VCSortedSub
                                y A ( j + 1 )
                            )
                          )
                          ->
                          (
                            (
                              (
                                0 <_ ( B - A )
                                /\
                                ( B - i ) < ( B - A )
                              )
                              /\
                              (
                                0 <_ i
                                /\
                                (
                                  i <_ B
                                  /\
                                  B < ( # ` y )
                                )
                              )
                            )
                            /\
                            A. z e. Word ZZ
                              (
                                ( # ` z ) = ( # ` y )
                                ->
                                (
                                  (
                                    (
                                      NTP4VCPermutSub
                                        y z i ( B + 1 )
                                    )
                                    /\
                                    (
                                      NTP4VCSortedSub
                                        z i ( B + 1 )
                                    )
                                  )
                                  ->
                                  (
                                    (
                                      NTP4VCPermutSub
                                        C z A ( B + 1 )
                                    )
                                    /\
                                    (
                                      NTP4VCSortedSub
                                        z A ( B + 1 )
                                    )
                                  )
                                )
                              )
                          )
                        )
                      )
                  )
                )
              )
      )
    )
    \/
    (
      -. ( A < B )
      /\
      (
        (
          NTP4VCPermutSub C C A ( B + 1 )
        )
        /\
        (
          NTP4VCSortedSub C A ( B + 1 )
        )
      )
    )
  ) $.
$}
