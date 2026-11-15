$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/flag2_Flag_swapqtvc: under the explicitly retained length and
  function-update premises for two writes, the color-list swap verification
  condition states that the selected entries are exchanged, every other
  entry is unchanged, and every color occurrence count is preserved on
  intervals containing both indices. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source color datatype is represented exactly by the three-element set
  0 through 2, and source color lists by arbitrary finite SetMM words over
  this carrier. NTP4VCToNat is Int.toNat, NTP4VCAt is source totalized list
  lookup with the arbitrary inhabited default color, and NTP4VCSet is the
  exact source List.set operation after conversion of its integer index.

  NTP4VCUpdateLaw is the source extensional function equality between a
  totalized lookup after List.set and Function.update of the old lookup.
  NTP4VCOcc is the cardinality of matching positions in a half-open integer
  interval. This is bidirectionally equivalent to the source nb_occ together
  with nb_occ'def: empty or reversed intervals have count zero, and extending
  a nonempty interval by its final position gives exactly the displayed
  recursive equation; conversely that recursion uniquely determines this
  finite cardinality.

  The final assertion preserves the source theorem's repeated bounds and the
  two nested implications whose premises state length preservation and the
  update law. All integer, list, color, and interval quantifiers retain their
  full source domains. It is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCColor NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCOcc
  NTP4VCUpdateLaw NTP4VCUnchanged NTP4VCOccPres NTP4VCSwapPost
$.

ntp4vc-color-syntax $a class NTP4VCColor $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-occ-syntax $a class ( NTP4VCOcc A B C D E ) $.

ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D E ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-occ-pres-syntax
  $a wff ( NTP4VCOccPres A B C D E ) $.
ntp4vc-swap-post-syntax
  $a wff ( NTP4VCSwapPost A B C D E ) $.

ntp4vc-color-definition $a |- NTP4VCColor = ( 0 ... 2 ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat C ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat C ) ) ,
  B
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
  $d k A B C D E $.

  ntp4vc-occ-definition $a |- (
    NTP4VCOcc A B C D E
  ) = (
    # `
    { k e. ( C ..^ D ) | ( NTP4VCAt A B k ) = E }
  ) $.
$}

${
  $d k A B C D E $.

  ntp4vc-update-law-definition $a |- (
    ( NTP4VCUpdateLaw A B C D E )
    <->
    A. k e. ZZ
      (
        ( NTP4VCAt A C k )
        =
        if (
          k = D ,
          E ,
          ( NTP4VCAt B C k )
        )
      )
  ) $.
$}

${
  $d k A B C D E $.

  ntp4vc-unchanged-definition $a |- (
    ( NTP4VCUnchanged A B C D E )
    <->
    A. k e. ZZ
      (
        (
          k =/= D
          /\
          k =/= E
        )
        ->
        ( NTP4VCAt B C k ) = ( NTP4VCAt A C k )
      )
  ) $.
$}

${
  $d x y c A B C D E $.

  ntp4vc-occ-pres-definition $a |- (
    ( NTP4VCOccPres A B C D E )
    <->
    A. x e. ZZ A. y e. ZZ A. c e. NTP4VCColor
      (
        (
          (
            x <_ D
            /\
            D < y
          )
          /\
          (
            x <_ E
            /\
            E < y
          )
        )
        ->
        (
          NTP4VCOcc B C x y c
        ) = (
          NTP4VCOcc A C x y c
        )
      )
  ) $.
$}

ntp4vc-swap-post-definition $a |- (
  ( NTP4VCSwapPost A B C D E )
  <->
  (
    ( NTP4VCAt B C D ) = ( NTP4VCAt A C E )
    /\
    (
      ( NTP4VCAt B C E ) = ( NTP4VCAt A C D )
      /\
      (
        ( NTP4VCUnchanged A B C D E )
        /\
        ( NTP4VCOccPres A B C D E )
      )
    )
  )
) $.

${
  $d k x y c A B C D $.

  $( Source parameters: A=a, B=the inhabited default color, C=i, D=j. $)

  ntp4vc-a-color-list
    $e |- A e. ( Word NTP4VCColor ) $.
  ntp4vc-default-color
    $e |- B e. NTP4VCColor $.
  ntp4vc-i-integer
    $e |- C e. ZZ $.
  ntp4vc-j-integer
    $e |- D e. ZZ $.

  ntp4vc-i-nonnegative
    $e |- 0 <_ C $.
  ntp4vc-i-in-bounds
    $e |- C < ( # ` A ) $.
  ntp4vc-j-nonnegative
    $e |- 0 <_ D $.
  ntp4vc-j-in-bounds
    $e |- D < ( # ` A ) $.

  ntp4vc-pearl-flag2-swap-vc $a |- (
    0 <_ C
    /\
    (
      C < ( # ` A )
      /\
      (
        (
          0 <_ D
          /\
          D < ( # ` A )
        )
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
              # ` (
                NTP4VCSet A C ( NTP4VCAt A B D )
              )
            ) = ( # ` A )
            ->
            (
              (
                NTP4VCUpdateLaw
                  ( NTP4VCSet A C ( NTP4VCAt A B D ) )
                  A B C ( NTP4VCAt A B D )
              )
              ->
              (
                (
                  0 <_ D
                  /\
                  D < (
                    # ` (
                      NTP4VCSet A C ( NTP4VCAt A B D )
                    )
                  )
                )
                /\
                (
                  (
                    # ` (
                      NTP4VCSet
                        ( NTP4VCSet A C ( NTP4VCAt A B D ) )
                        D
                        ( NTP4VCAt A B C )
                    )
                  ) = (
                    # ` (
                      NTP4VCSet A C ( NTP4VCAt A B D )
                    )
                  )
                  ->
                  (
                    (
                      NTP4VCUpdateLaw
                        (
                          NTP4VCSet
                            ( NTP4VCSet A C ( NTP4VCAt A B D ) )
                            D
                            ( NTP4VCAt A B C )
                        )
                        ( NTP4VCSet A C ( NTP4VCAt A B D ) )
                        B D ( NTP4VCAt A B C )
                    )
                    ->
                    (
                      NTP4VCSwapPost
                        A
                        (
                          NTP4VCSet
                            ( NTP4VCSet A C ( NTP4VCAt A B D ) )
                            D
                            ( NTP4VCAt A B C )
                        )
                        B C D
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
