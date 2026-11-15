$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_Quicksort_quicksortqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_shearsort_Quicksort_quicksortqtvc):
  the top-level quicksort verification condition states that any same-length
  integer list satisfying the full-range sortedness and permutation
  postconditions is a sorted permutation of the input. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer lists. NTP4VCToNat,
  NTP4VCAt, and NTP4VCSlice reproduce the source Int.toNat, totalized list
  lookup with default zero, and drop-then-take slice.

  NTP4VCPerm compares the multiplicity of every integer and includes equal
  length, so on finite integer words it is equivalent in both directions to
  List.Perm. NTP4VCPermutSub is exactly the exported permut_sub' predicate:
  equal lengths, unchanged prefix and suffix slices, and a permutation of the
  selected middle slices. NTP4VCSortedSub is the source integer-indexed
  sorted_sub1 predicate, and NTP4VCSorted is its full-list specialization.

  The let-bound endpoint o1 is replaced by the equal term # ` A. The first
  conjunct retains all three source bounds, and the internally universal
  output list remains under the same two nested implications. Expanding the
  definitions recovers the complete Lean, Rocq, and Isabelle proposition and
  the top-level Why3 quicksort contract. The final declaration is Metamath's
  native unproved $a statement encoding; every preceding $a is syntax or a
  faithful definition required to state it, and this database contains no $p
  declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice
  NTP4VCAt NTP4VCPerm NTP4VCPermutSub
  NTP4VCSortedSub NTP4VCSorted
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax
  $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax
  $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax
  $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax
  $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax
  $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-permut-sub-syntax
  $a wff ( NTP4VCPermutSub A B C D ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A ) $.

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

ntp4vc-sorted-definition $a |- (
  ( NTP4VCSorted A )
  <->
  ( NTP4VCSortedSub A 0 ( # ` A ) )
) $.

${
  $d A B $.

  ntp4vc-input-list $e |- A e. Word ZZ $.

  ntp4vc-pearl-verifythis-2021-shearsort-quicksort-quicksort-vc $a |- (
    (
      0 <_ 0
      /\
      (
        0 <_ ( # ` A )
        /\
        ( # ` A ) <_ ( # ` A )
      )
    )
    /\
    A. B e. Word ZZ
      (
        ( # ` B ) = ( # ` A )
        ->
        (
          (
            ( NTP4VCSortedSub B 0 ( # ` A ) )
            /\
            (
              NTP4VCPermutSub
                A
                B
                0
                ( NTP4VCToNat ( # ` A ) )
            )
          )
          ->
          (
            ( NTP4VCSorted B )
            /\
            ( NTP4VCPerm A B )
          )
        )
      )
  ) $.
$}
