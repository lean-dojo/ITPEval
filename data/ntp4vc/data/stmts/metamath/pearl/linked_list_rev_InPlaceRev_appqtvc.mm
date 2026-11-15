$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRev_appqtvc: the in-place linked-list append
  verification condition for two disjoint inductively defined list segments,
  including the empty-head case, head-tail decomposition, traversal, pointer
  update, and preservation of the combined segment. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  H is the arbitrary inhabited source carrier loc. SetMM Word H is exactly
  the full type of arbitrary finite zero-based location lists. A is the total
  next-location function, F is null, and G is the Boolean equality test with
  its complete source specification. Booleans use the exact two-element
  carrier 2, with true represented by 1.

  NTP4VCDisjoint is equivalent to the source membership definition by the
  finite-word indexing characterization. NTP4VCListSeg is bidirectionally
  equivalent to the source inductive relation: the empty word ends at its
  starting location, while a nonempty word begins at that location, contains
  only non-null locations, follows A between adjacent entries, and ends where
  A maps its last entry. NTP4VCUpdate is full-domain pointwise function
  update.

  The source let-bound empty word and Boolean tests are substituted
  definitionally. Each proposition-valued conditional is expanded into its
  exhaustive guarded branches. The nonempty pM match remains an internal
  existential head-tail decomposition over Word H; its empty branch is false,
  and the repeated inner match tail equality is retained as t = t. Thus no
  source witness is moved to an external parameter.

  The unused no_repet definition does not occur in the assumptions or
  conclusion of this verification condition and is omitted. Every auxiliary
  $a declaration below is syntax or an explicit definitional abbreviation.
  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p declaration.
$)

$c
  NTP4VCUpdate NTP4VCDisjoint NTP4VCListSeg
  NTP4VCMatchStep NTP4VCElse NTP4VCAppVC
$.

ntp4vc-update-syntax
  $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-disjoint-syntax
  $a wff ( NTP4VCDisjoint A B ) $.
ntp4vc-list-seg-syntax
  $a wff ( NTP4VCListSeg A B C D E ) $.
ntp4vc-match-step-syntax
  $a wff ( NTP4VCMatchStep A B C D E F G H ) $.
ntp4vc-else-syntax
  $a wff ( NTP4VCElse A B C D E F G H ) $.
ntp4vc-app-vc-syntax
  $a wff ( NTP4VCAppVC A B C D E F G H ) $.

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
        E = ( <" h "> ++ t )
        /\
        (
          F =/= G
          /\
          (
            t = t
            /\
            (
              ( A ` F ) =/= G
              /\
              (
                ( NTP4VCListSeg
                  A B ( D ++ <" h "> ) ( A ` F ) G
                )
                /\
                (
                  ( NTP4VCListSeg A ( A ` F ) t G G )
                  /\
                  (
                    (
                      ( D ++ <" h "> )
                      ++
                      t
                    )
                    =
                    C
                    /\
                    ( NTP4VCDisjoint
                      ( D ++ <" h "> )
                      t
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
                    (
                      NTP4VCMatchStep
                        A B C r s p F H
                    )
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
     H=loc, A=next, B=l1, C=l1M, D=l2, E=l2M,
     F=null, and G=eq_loc. $)

  ntp4vc-location-carrier-nonempty $e |- H =/= (/) $.
  ntp4vc-next-function $e |- A e. ( H ^m H ) $.
  ntp4vc-l1-location $e |- B e. H $.
  ntp4vc-l1m-list $e |- C e. Word H $.
  ntp4vc-l2-location $e |- D e. H $.
  ntp4vc-l2m-list $e |- E e. Word H $.
  ntp4vc-null-location $e |- F e. H $.
  ntp4vc-eq-loc-function $e |- G e. ( { 0 , 1 } ^m ( H X. H ) ) $.

  ntp4vc-eq-loc-spec $e |- A. x e. H A. y e. H
    (
      ( G ` <. x , y >. ) = 1
      <->
      x = y
    ) $.

  ntp4vc-fact0 $e |- ( NTP4VCListSeg A B C F F ) $.
  ntp4vc-fact1 $e |- ( NTP4VCListSeg A D E F F ) $.
  ntp4vc-fact2 $e |- ( NTP4VCDisjoint C E ) $.

  ntp4vc-pearl-linked-list-rev-in-place-rev-app-vc $a |- (
    NTP4VCAppVC A B C D E F G H
  ) $.
$}
