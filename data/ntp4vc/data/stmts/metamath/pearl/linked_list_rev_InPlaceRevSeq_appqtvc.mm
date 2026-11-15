$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRevSeq_appqtvc: the in-place linked-list
  reversal sequence verification condition for appending two disjoint list
  segments, including the empty-head case, one-step traversal, tail
  decomposition, pointer update, and preservation of the combined segment.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  H is the arbitrary inhabited source carrier loc. SetMM Word H is exactly
  the full type of arbitrary finite zero-based location lists. A is the total
  next-location function, F is null, and G is the Boolean equality test with
  its complete source specification. Booleans use the exact two-element
  carrier 2, with true represented by 1.

  NTP4VCDisjoint and NTP4VCListSeg directly expand the source definitions.
  All integer indices remain quantified over the full unbounded domain ZZ;
  every list access occurs under the same nonnegative in-bounds guard as in
  the source. NTP4VCTail is drop 1 on finite words, and NTP4VCUpdate is the
  full-domain pointwise function update.

  The source let-bound empty word, singleton word, appended prefix, Boolean
  tests, and next-location value are substituted definitionally. The two
  proposition-valued conditionals are expanded into exhaustive guarded
  disjunctions. NTP4VCSingletonLaws and NTP4VCAppendLaws retain the generated
  length and pointwise premises even where they are derivable from SetMM word
  operations. The universally quantified decomposition lists and location
  remain internal to NTP4VCElse, exactly as in the source theorem.

  The unused result, no_repet, memory, and next-type declarations do not occur
  in the assumptions or conclusion of this verification condition and are
  omitted. Every auxiliary $a declaration below is syntax or an explicit
  definitional abbreviation. The final $a declaration is Metamath's native
  unproved statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCTail NTP4VCUpdate NTP4VCDisjoint NTP4VCListSeg
  NTP4VCSingletonLaws NTP4VCAppendLaws NTP4VCAdvance
  NTP4VCThen NTP4VCElse NTP4VCAppVC
$.

ntp4vc-tail-syntax
  $a class ( NTP4VCTail A ) $.
ntp4vc-update-syntax
  $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-disjoint-syntax
  $a wff ( NTP4VCDisjoint A B ) $.
ntp4vc-list-seg-syntax
  $a wff ( NTP4VCListSeg A B C D E ) $.
ntp4vc-singleton-laws-syntax
  $a wff ( NTP4VCSingletonLaws A ) $.
ntp4vc-append-laws-syntax
  $a wff ( NTP4VCAppendLaws A B ) $.
ntp4vc-advance-syntax
  $a wff ( NTP4VCAdvance A B C D E F G ) $.
ntp4vc-then-syntax
  $a wff ( NTP4VCThen A B C D E F G ) $.
ntp4vc-else-syntax
  $a wff ( NTP4VCElse A B C D E F G H ) $.
ntp4vc-app-vc-syntax
  $a wff ( NTP4VCAppVC A B C D E F G H ) $.

${
  $d i A $.

  ntp4vc-tail-definition $a |- (
    NTP4VCTail A
  ) = (
    i e. ( 0 ..^ ( ( # ` A ) - 1 ) ) |->
      ( A ` ( i + 1 ) )
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
  $d i A $.

  ntp4vc-singleton-laws-definition $a |- (
    NTP4VCSingletonLaws A
  ) <-> (
    (
      ( # ` <" A "> )
      =
      ( 1 + ( # ` (/) ) )
    )
    /\
    (
      ( <" A "> ` 0 ) = A
      /\
      A. i e. ZZ
        (
          (
            0 < i
            /\
            i <_ ( # ` (/) )
          )
          ->
          ( <" A "> ` i ) = ( (/) ` ( i - 1 ) )
        )
    )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-append-laws-definition $a |- (
    NTP4VCAppendLaws A B
  ) <-> (
    (
      ( # ` ( A ++ <" B "> ) )
      =
      ( ( # ` A ) + ( # ` <" B "> ) )
    )
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          ->
          ( ( A ++ <" B "> ) ` i ) = ( A ` i )
        )
      /\
      A. i e. ZZ
        (
          (
            ( # ` A ) <_ i
            /\
            i < ( # ` ( A ++ <" B "> ) )
          )
          ->
          (
            ( A ++ <" B "> ) ` i
          )
          =
          (
            <" B "> ` ( i - ( # ` A ) )
          )
        )
    )
  ) $.
$}

ntp4vc-advance-definition $a |- (
  NTP4VCAdvance A B C D E F G
) <-> (
  F =/= G
  /\
  (
    (
      0 <_ ( # ` E )
      /\
      ( # ` ( NTP4VCTail E ) ) < ( # ` E )
    )
    /\
    (
      ( A ` F ) =/= G
      /\
      (
        ( NTP4VCListSeg
          A B ( D ++ <" F "> ) ( A ` F ) G
        )
        /\
        (
          ( NTP4VCListSeg
            A ( A ` F ) ( NTP4VCTail E ) G G
          )
          /\
          (
            (
              ( D ++ <" F "> )
              ++
              ( NTP4VCTail E )
            )
            =
            C
            /\
            ( NTP4VCDisjoint
              ( D ++ <" F "> )
              ( NTP4VCTail E )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-then-definition $a |- (
  NTP4VCThen A B C D E F G
) <-> (
  (
    0 <_ 1
    /\
    1 <_ ( # ` E )
  )
  /\
  (
    ( NTP4VCSingletonLaws F )
    ->
    (
      ( NTP4VCAppendLaws D F )
      ->
      ( NTP4VCAdvance A B C D E F G )
    )
  )
) $.

${
  $d p r s A B C D E F G H $.

  ntp4vc-else-definition $a |- (
    NTP4VCElse A B C D E F G H
  ) <-> (
    (
      B =/= F
      /\
      (
        ( NTP4VCListSeg A B (/) B F )
        /\
        (
          ( NTP4VCListSeg A B C F F )
          /\
          (
            ( (/) ++ C ) = C
            /\
            ( NTP4VCDisjoint (/) C )
          )
        )
      )
    )
    /\
    A. r e. Word H
      A. s e. Word H
        A. p e. H
          (
            (
              p =/= F
              /\
              (
                ( NTP4VCListSeg A B r p F )
                /\
                (
                  ( NTP4VCListSeg A p s F F )
                  /\
                  (
                    ( r ++ s ) = C
                    /\
                    ( NTP4VCDisjoint r s )
                  )
                )
              )
            )
            ->
            (
              p =/= F
              /\
              (
                (
                  ( G ` <. ( A ` p ) , F >. ) = 1
                  <->
                  ( A ` p ) = F
                )
                ->
                (
                  (
                    ( G ` <. ( A ` p ) , F >. ) =/= 1
                    /\
                    ( NTP4VCThen A B C r s p F )
                  )
                  \/
                  (
                    ( G ` <. ( A ` p ) , F >. ) = 1
                    /\
                    (
                      p =/= F
                      /\
                      ( NTP4VCListSeg
                        ( NTP4VCUpdate A p D H )
                        B
                        ( C ++ E )
                        F
                        F
                      )
                    )
                  )
                )
              )
            )
          )
  ) $.
$}

ntp4vc-app-vc-definition $a |- (
  NTP4VCAppVC A B C D E F G H
) <-> (
  (
    ( G ` <. B , F >. ) = 1
    <->
    B = F
  )
  ->
  (
    (
      ( G ` <. B , F >. ) = 1
      /\
      ( NTP4VCListSeg A D ( C ++ E ) F F )
    )
    \/
    (
      ( G ` <. B , F >. ) =/= 1
      /\
      ( NTP4VCElse A B C D E F G H )
    )
  )
) $.

${
  $d x y A B C D E F G H $.

  $( Source carrier and declarations:
     H=loc, A=next1, B=l1, C=l1M, D=l2, E=l2M,
     F=null, and G=eq_loc. $)

  ntp4vc-location-carrier-nonempty $e |- H =/= (/) $.
  ntp4vc-next-function $e |- A e. ( H ^m H ) $.
  ntp4vc-l1-location $e |- B e. H $.
  ntp4vc-l1m-list $e |- C e. Word H $.
  ntp4vc-l2-location $e |- D e. H $.
  ntp4vc-l2m-list $e |- E e. Word H $.
  ntp4vc-null-location $e |- F e. H $.
  ntp4vc-eq-loc-function $e |- G e. ( 2 ^m ( H X. H ) ) $.

  ntp4vc-eq-loc-spec $e |- A. x e. H A. y e. H
    (
      ( G ` <. x , y >. ) = 1
      <->
      x = y
    ) $.

  ntp4vc-fact0 $e |- ( NTP4VCListSeg A B C F F ) $.
  ntp4vc-fact1 $e |- ( NTP4VCListSeg A D E F F ) $.
  ntp4vc-fact2 $e |- ( NTP4VCDisjoint C E ) $.

  ntp4vc-pearl-linked-list-rev-in-place-rev-seq-app-vc $a |- (
    NTP4VCAppVC A B C D E F G H
  ) $.
$}
