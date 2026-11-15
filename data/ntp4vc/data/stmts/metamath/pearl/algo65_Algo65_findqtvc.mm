$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/algo65_Algo65_findqtvc: the find verification condition states the
  nested partition and pivot-selection obligations for an integer-list
  segment around the value 42, preserving the segment's permutation and
  ordering every element on the two sides of the selected index.
  This file contains no proof.
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
  selected middle slice.

  NTP4VCPartition directly expands the segment permutation and the three
  source regions relative to 42; the bounds m <= j < i <= n remain explicit
  in the main assertion. NTP4VCPivoted directly expands a segment permutation
  together with the two universal pivot-order conditions. The
  proposition-valued source if expressions are represented by equivalent
  guarded disjunctions. Splitting the theorem's typed parameters and four
  assumptions into scoped essential hypotheses is bidirectionally equivalent
  to the source curried theorem. Every integer and word quantifier retains its
  full source domain. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice NTP4VCAt
  NTP4VCPerm NTP4VCPermutSub NTP4VCPartition NTP4VCPivoted
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
ntp4vc-partition-syntax
  $a wff ( NTP4VCPartition A B C D E F G ) $.
ntp4vc-pivoted-syntax
  $a wff ( NTP4VCPivoted A B C D E ) $.

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
  $d q A B C $.

  ntp4vc-slice-definition $a |- (
    NTP4VCSlice A B C
  ) = (
    q e. ( 0 ..^ ( NTP4VCSliceLen A B C ) ) |->
      ( A ` ( ( NTP4VCSliceStart A B ) + q ) )
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
  $d q v A B $.

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
              { q e. ( 0 ..^ ( # ` A ) ) | ( A ` q ) = v }
            )
            =
            (
              # `
              { q e. ( 0 ..^ ( # ` B ) ) | ( B ` q ) = v }
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
  $d r A B C D E F G $.

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
            A. r e. ZZ
              (
                ( C <_ r /\ r <_ F )
                ->
                ( NTP4VCAt B r ) <_ G
              )
            /\
            (
              A. r e. ZZ
                (
                  ( F < r /\ r < E )
                  ->
                  ( NTP4VCAt B r ) = G
                )
              /\
              A. r e. ZZ
                (
                  ( E <_ r /\ r <_ D )
                  ->
                  G <_ ( NTP4VCAt B r )
                )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d r A B C D E $.

  ntp4vc-pivoted-definition $a |- (
    ( NTP4VCPivoted A B C D E )
    <->
    (
      ( NTP4VCPermutSub A B C ( E + 1 ) )
      /\
      (
        A. r e. ZZ
          (
            ( C <_ r /\ r <_ D )
            ->
            ( NTP4VCAt B r ) <_ ( NTP4VCAt B D )
          )
        /\
        A. r e. ZZ
          (
            ( D <_ r /\ r <_ E )
            ->
            ( NTP4VCAt B D ) <_ ( NTP4VCAt B r )
          )
      )
    )
  ) $.
$}

${
  $d i j x y z A B C D $.

  $( Source parameters: A=m, B=k, C=n, and D=a. $)

  ntp4vc-m-integer $e |- A e. ZZ $.
  ntp4vc-k-integer $e |- B e. ZZ $.
  ntp4vc-n-integer $e |- C e. ZZ $.
  ntp4vc-a-list $e |- D e. Word ZZ $.

  ntp4vc-m-nonnegative $e |- 0 <_ A $.
  ntp4vc-m-le-k $e |- A <_ B $.
  ntp4vc-k-le-n $e |- B <_ C $.
  ntp4vc-n-in-bounds $e |- C < ( # ` D ) $.

  ntp4vc-pearl-algo65-find-vc $a |- (
    (
      A < C
      /\
      (
        (
          0 <_ A
          /\
          (
            A < C
            /\
            C < ( # ` D )
          )
        )
        /\
        A. j e. ZZ
          A. i e. ZZ
            A. x e. Word ZZ
              (
                ( # ` x ) = ( # ` D )
                ->
                (
                  (
                    (
                      A <_ j
                      /\
                      (
                        j < i
                        /\
                        i <_ C
                      )
                    )
                    /\
                    (
                      NTP4VCPartition
                        D x A C i j ; 4 2
                    )
                  )
                  ->
                  (
                    (
                      B <_ j
                      /\
                      (
                        (
                          (
                            0 <_ ( C - A )
                            /\
                            ( j - A ) < ( C - A )
                          )
                          /\
                          (
                            0 <_ A
                            /\
                            (
                              A <_ B
                              /\
                              (
                                B <_ j
                                /\
                                j < ( # ` x )
                              )
                            )
                          )
                        )
                        /\
                        A. y e. Word ZZ
                          (
                            ( # ` y ) = ( # ` x )
                            ->
                            (
                              ( NTP4VCPivoted x y A B j )
                              ->
                              (
                                (
                                  i <_ B
                                  /\
                                  (
                                    (
                                      (
                                        0 <_ ( C - A )
                                        /\
                                        ( C - i ) < ( C - A )
                                      )
                                      /\
                                      (
                                        0 <_ i
                                        /\
                                        (
                                          i <_ B
                                          /\
                                          (
                                            B <_ C
                                            /\
                                            C < ( # ` y )
                                          )
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
                                            NTP4VCPivoted y z i B C
                                          )
                                          ->
                                          (
                                            NTP4VCPivoted D z A B C
                                          )
                                        )
                                      )
                                  )
                                )
                                \/
                                (
                                  -. ( i <_ B )
                                  /\
                                  (
                                    NTP4VCPivoted D y A B C
                                  )
                                )
                              )
                            )
                          )
                      )
                    )
                    \/
                    (
                      -. ( B <_ j )
                      /\
                      (
                        (
                          i <_ B
                          /\
                          (
                            (
                              (
                                0 <_ ( C - A )
                                /\
                                ( C - i ) < ( C - A )
                              )
                              /\
                              (
                                0 <_ i
                                /\
                                (
                                  i <_ B
                                  /\
                                  (
                                    B <_ C
                                    /\
                                    C < ( # ` x )
                                  )
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
                                    NTP4VCPivoted x y i B C
                                  )
                                  ->
                                  (
                                    NTP4VCPivoted D y A B C
                                  )
                                )
                              )
                          )
                        )
                        \/
                        (
                          -. ( i <_ B )
                          /\
                          (
                            NTP4VCPivoted D x A B C
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
      -. ( A < C )
      /\
      (
        NTP4VCPivoted D D A B C
      )
    )
  ) $.
$}
