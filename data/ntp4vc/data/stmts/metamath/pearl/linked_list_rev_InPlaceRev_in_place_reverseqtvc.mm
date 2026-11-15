$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRev_in_place_reverseqtvc: the in-place
  linked-list reversal verification condition establishes the empty
  accumulator invariants and preserves the list-segment, disjointness, and
  reversal invariant through a pointer update, with the reversed segment at
  loop exit. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  H is the arbitrary inhabited source carrier loc. SetMM Word H is exactly
  the full type of arbitrary finite zero-based location lists. A is a total
  next-location function, D is null, and E is the Boolean equality test with
  its complete source specification. Booleans use the exact two-element
  carrier 2, with true represented by 1.

  NTP4VCReverse, NTP4VCUpdate, NTP4VCDisjoint, and NTP4VCListSeg directly
  encode the corresponding source operations and definitions. All integer
  indices retain the full unbounded domain ZZ. The source match on pM keeps
  its nonempty head and tail existentially quantified inside
  NTP4VCMatchStep; the repeated inner match tail equation is retained as
  t = t.

  The proposition-valued conditional is expanded into exhaustive guarded
  branches. The loop lists, locations, and next function remain universally
  quantified inside NTP4VCLoop, exactly as in the source theorem. The unused
  no_repet definition does not occur in the theorem assumption or conclusion
  and is omitted. Every auxiliary $a declaration below is syntax or an
  explicit definitional abbreviation. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCReverse NTP4VCUpdate NTP4VCDisjoint NTP4VCListSeg
  NTP4VCMatchStep NTP4VCThen NTP4VCBranch NTP4VCLoop
  NTP4VCInPlaceReverseVC
$.

ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-update-syntax
  $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-disjoint-syntax
  $a wff ( NTP4VCDisjoint A B ) $.
ntp4vc-list-seg-syntax
  $a wff ( NTP4VCListSeg A B C D E ) $.
ntp4vc-match-step-syntax
  $a wff ( NTP4VCMatchStep A B C D E F G H ) $.
ntp4vc-then-syntax
  $a wff ( NTP4VCThen A B C D E F G H ) $.
ntp4vc-branch-syntax
  $a wff ( NTP4VCBranch A B C D E F G H I ) $.
ntp4vc-loop-syntax
  $a wff ( NTP4VCLoop A B C D ) $.
ntp4vc-in-place-reverse-vc-syntax
  $a wff ( NTP4VCInPlaceReverseVC A B C D E F ) $.

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

${
  $d x A B C D $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C D
  ) = (
    x e. D |->
      if ( x = B , C , ( A ` x ) )
  ) $.
$}

${
  $d i j A B $.

  ntp4vc-disjoint-definition $a |- (
    NTP4VCDisjoint A B
  ) <-> (
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
              0 <_ j
              /\
              j < ( # ` B )
            )
            ->
            ( A ` i ) =/= ( B ` j )
          )
      )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-list-seg-definition $a |- (
    NTP4VCListSeg A B C D E
  ) <-> (
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` C )
          )
          ->
          ( C ` i ) =/= E
        )
    )
    /\
    (
      (
        B = D
        /\
        ( # ` C ) = 0
      )
      \/
      (
        1 <_ ( # ` C )
        /\
        (
          ( C ` 0 ) = B
          /\
          (
            ( A ` ( C ` ( ( # ` C ) - 1 ) ) ) = D
            /\
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i < ( ( # ` C ) - 1 )
                )
                ->
                ( A ` ( C ` i ) ) = ( C ` ( i + 1 ) )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d h t A B C D E F G H $.

  ntp4vc-match-step-definition $a |- (
    NTP4VCMatchStep A B C D E F G H
  ) <-> (
    E. h e. H E. t e. Word H
      (
        D = ( <" h "> ++ t )
        /\
        (
          t = t
          /\
          (
            ( NTP4VCListSeg
              ( NTP4VCUpdate A E C H )
              ( A ` E )
              t
              G
              G
            )
            /\
            (
              ( NTP4VCListSeg
                ( NTP4VCUpdate A E C H )
                E
                ( <" h "> ++ B )
                G
                G
              )
              /\
              (
                ( NTP4VCDisjoint t ( <" h "> ++ B ) )
                /\
                (
                  (
                    ( NTP4VCReverse t )
                    ++
                    ( <" h "> ++ B )
                  )
                  =
                  ( NTP4VCReverse F )
                )
              )
            )
          )
        )
      )
  ) $.
$}

ntp4vc-then-definition $a |- (
  NTP4VCThen A B C D E F G H
) <-> (
  E =/= G
  /\
  ( NTP4VCMatchStep A B C D E F G H )
) $.

ntp4vc-branch-definition $a |- (
  NTP4VCBranch A B C D E F G H I
) <-> (
  (
    ( I ` <. E , G >. ) =/= 1
    /\
    ( NTP4VCThen A B C D E F G H )
  )
  \/
  (
    ( I ` <. E , G >. ) = 1
    /\
    ( NTP4VCListSeg A C ( NTP4VCReverse F ) G G )
  )
) $.

${
  $d n p r s x A B C D $.

  ntp4vc-loop-definition $a |- (
    NTP4VCLoop A B C D
  ) <-> (
    A. r e. Word D
      A. x e. D
        A. s e. Word D
          A. p e. D
            A. n e. ( D ^m D )
              (
                (
                  ( NTP4VCListSeg n p s B B )
                  /\
                  (
                    ( NTP4VCListSeg n x r B B )
                    /\
                    (
                      ( NTP4VCDisjoint s r )
                      /\
                      (
                        (
                          ( NTP4VCReverse s )
                          ++
                          r
                        )
                        =
                        ( NTP4VCReverse A )
                      )
                    )
                  )
                )
                ->
                (
                  (
                    ( C ` <. p , B >. ) = 1
                    <->
                    p = B
                  )
                  ->
                  (
                    NTP4VCBranch n r x s p A B D C
                  )
                )
              )
  ) $.
$}

ntp4vc-in-place-reverse-vc-definition $a |- (
  NTP4VCInPlaceReverseVC A B C D E F
) <-> (
  ( NTP4VCListSeg A B C D D )
  /\
  (
    ( NTP4VCListSeg A D (/) D D )
    /\
    (
      ( NTP4VCDisjoint C (/) )
      /\
      (
        (
          ( ( NTP4VCReverse C ) ++ (/) )
          =
          ( NTP4VCReverse C )
        )
        /\
        ( NTP4VCLoop C D E F )
      )
    )
  )
) $.

${
  $d x y A B C D E F $.

  $( Source carrier and declarations:
     F=loc, A=next, B=l, C=lM, D=null, and E=eq_loc. $)

  ntp4vc-location-carrier-nonempty $e |- F =/= (/) $.
  ntp4vc-next-function $e |- A e. ( F ^m F ) $.
  ntp4vc-l-location $e |- B e. F $.
  ntp4vc-lm-list $e |- C e. Word F $.
  ntp4vc-null-location $e |- D e. F $.
  ntp4vc-eq-loc-function $e |- E e. ( { 0 , 1 } ^m ( F X. F ) ) $.

  ntp4vc-eq-loc-spec $e |- A. x e. F A. y e. F
    (
      ( E ` <. x , y >. ) = 1
      <->
      x = y
    ) $.

  ntp4vc-fact0 $e |- ( NTP4VCListSeg A B C D D ) $.

  ntp4vc-pearl-linked-list-rev-in-place-rev-in-place-reverse-vc
    $a |- ( NTP4VCInPlaceReverseVC A B C D E F ) $.
$}
