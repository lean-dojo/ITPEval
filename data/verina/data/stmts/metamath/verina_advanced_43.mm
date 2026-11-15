$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_43 (verina__metamath__verina_advanced_43), catalog title
  maxStrength: exact bitmask subset enumeration, nonempty filtering, integer
  product folds, and a defaulted maximum compute the greatest product of a
  nonempty subsequence of an arbitrary nonempty finite integer list. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA43BitSet expresses the source test
    (mask.shiftRight i).land 1 == 1.
  VERINA43ImplMaskWordGraph selects precisely the input positions whose
  same-numbered mask bits are set, in increasing input-index order. Thus
  VERINA43PowerSetGraph records, in numeric mask order from zero through
  2^n-1, exactly the word produced by the local powerSet helper's range,
  map, and foldr. VERINA43NonEmptySubsetsGraph is its stable filter by
  nonemptiness; mask zero is the unique removed entry.

  VERINA43ProductGraph records List.foldl multiplication from integer one.
  VERINA43ProductsGraph maps that exact fold over the filtered subsets.
  VERINA43MaxGetDGraph is List.max? followed by getD (-1000000): it returns
  the default exactly on an empty product word and otherwise the occurring
  integer that bounds every entry above. VERINA43MaxStrength composes these
  independently specified executable stages.

  The source postcondition uses List.sublists, whose recursive ordering is
  represented by VERINA43PostMaskWordGraph: input position k corresponds
  to mask bit n-1-k. VERINA43SublistsGraph lists all such subsequences in
  numeric mask order, VERINA43NonEmptySublistsGraph performs the exact
  stable nonempty filter, and VERINA43PostProductsGraph maps the same
  product fold. VERINA43Post then reproduces List.contains for the result
  and List.all asserting that every product is at most it.

  VERINA43Pre is the source nonempty-list precondition. The proof-valued
  precondition argument is computationally and propositionally unused and
  is omitted from the target function and postcondition predicate. The final
  $a declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA43BitSet
  VERINA43ImplMaskWordGraph
  VERINA43PowerSetGraph VERINA43PowerSet
  VERINA43NonEmptySubsetsGraph VERINA43NonEmptySubsets
  VERINA43ProductGraph VERINA43Product
  VERINA43ProductsGraph VERINA43Products
  VERINA43MaxGetDGraph VERINA43MaxGetD
  VERINA43Pre VERINA43MaxStrength
  VERINA43PostMaskWordGraph
  VERINA43SublistsGraph VERINA43Sublists
  VERINA43NonEmptySublistsGraph VERINA43NonEmptySublists
  VERINA43PostProductsGraph VERINA43PostProducts
  VERINA43Post
$.

verina43-bit-set-syntax
  $a wff ( VERINA43BitSet A B ) $.
verina43-impl-mask-word-graph-syntax
  $a wff ( VERINA43ImplMaskWordGraph A B C ) $.
verina43-power-set-graph-syntax
  $a wff ( VERINA43PowerSetGraph A B ) $.
verina43-power-set-syntax
  $a class ( VERINA43PowerSet A ) $.
verina43-nonempty-subsets-graph-syntax
  $a wff ( VERINA43NonEmptySubsetsGraph A B ) $.
verina43-nonempty-subsets-syntax
  $a class ( VERINA43NonEmptySubsets A ) $.
verina43-product-graph-syntax
  $a wff ( VERINA43ProductGraph A B ) $.
verina43-product-syntax
  $a class ( VERINA43Product A ) $.
verina43-products-graph-syntax
  $a wff ( VERINA43ProductsGraph A B ) $.
verina43-products-syntax
  $a class ( VERINA43Products A ) $.
verina43-max-get-d-graph-syntax
  $a wff ( VERINA43MaxGetDGraph A B ) $.
verina43-max-get-d-syntax
  $a class ( VERINA43MaxGetD A ) $.
verina43-precondition-syntax
  $a wff ( VERINA43Pre A ) $.
verina43-max-strength-syntax
  $a class ( VERINA43MaxStrength A ) $.
verina43-post-mask-word-graph-syntax
  $a wff ( VERINA43PostMaskWordGraph A B C ) $.
verina43-sublists-graph-syntax
  $a wff ( VERINA43SublistsGraph A B ) $.
verina43-sublists-syntax
  $a class ( VERINA43Sublists A ) $.
verina43-nonempty-sublists-graph-syntax
  $a wff ( VERINA43NonEmptySublistsGraph A B ) $.
verina43-nonempty-sublists-syntax
  $a class ( VERINA43NonEmptySublists A ) $.
verina43-post-products-graph-syntax
  $a wff ( VERINA43PostProductsGraph A B ) $.
verina43-post-products-syntax
  $a class ( VERINA43PostProducts A ) $.
verina43-postcondition-syntax
  $a wff ( VERINA43Post A B ) $.

verina43-bit-set-definition $a |- (
  VERINA43BitSet A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2
  ) = 1
) $.

${
  $d i j k p A B C $.

  verina43-impl-mask-word-graph-definition $a |- (
    VERINA43ImplMaskWordGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ( 0 ..^ ( 2 ^ ( # ` A ) ) )
      )
      /\
      C e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` C )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              ( p ` i ) < ( # ` A )
              /\
              ( C ` i ) = ( A ` ( p ` i ) )
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            A. j e. ( 0 ..^ ( # ` p ) )
              (
                i < j
                ->
                ( p ` i ) < ( p ` j )
              )
          /\
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              ( VERINA43BitSet B k )
              <->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = k
            )
        )
      )
  ) $.
$}

${
  $d r A B $.

  verina43-power-set-graph-definition $a |- (
    VERINA43PowerSetGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    (
      ( # ` B ) = ( 2 ^ ( # ` A ) )
      /\
      A. r e. ( 0 ..^ ( # ` B ) )
        (
          VERINA43ImplMaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina43-power-set-definition $a |- (
    VERINA43PowerSet A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA43PowerSetGraph A y )
  ) $.
$}

${
  $d j A B $.

  verina43-nonempty-subsets-graph-definition $a |- (
    VERINA43NonEmptySubsetsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    (
      ( # ` B ) = ( ( # ` ( VERINA43PowerSet A ) ) - 1 )
      /\
      A. j e. ( 0 ..^ ( # ` B ) )
        (
          B ` j
        ) = (
          ( VERINA43PowerSet A ) ` ( j + 1 )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina43-nonempty-subsets-definition $a |- (
    VERINA43NonEmptySubsets A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA43NonEmptySubsetsGraph A y )
  ) $.
$}

${
  $d k s A B $.

  verina43-product-graph-definition $a |- (
    VERINA43ProductGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. s e. Word ZZ
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 1
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = (
              ( s ` k ) x. ( A ` k )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina43-product-definition $a |- (
    VERINA43Product A
  ) = (
    iota_ y e. ZZ
      ( VERINA43ProductGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina43-products-graph-definition $a |- (
    VERINA43ProductsGraph A B
  ) <-> (
    (
      A e. Word ( Word ZZ )
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        (
          B ` k
        ) = (
          VERINA43Product ( A ` k )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina43-products-definition $a |- (
    VERINA43Products A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA43ProductsGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina43-max-get-d-graph-definition $a |- (
    VERINA43MaxGetDGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      (
        ( # ` A ) = 0
        /\
        B = ( -u ( ; ; ; ; ; ; 1 0 0 0 0 0 0 ) )
      )
      \/
      (
        (
          0 < ( # ` A )
          /\
          B e. ran A
        )
        /\
        A. k e. ( 0 ..^ ( # ` A ) )
          ( A ` k ) <_ B
      )
    )
  ) $.
$}

${
  $d y A $.

  verina43-max-get-d-definition $a |- (
    VERINA43MaxGetD A
  ) = (
    iota_ y e. ZZ
      ( VERINA43MaxGetDGraph A y )
  ) $.
$}

verina43-precondition-definition $a |- (
  VERINA43Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verina43-max-strength-definition $a |- (
  VERINA43MaxStrength A
) = (
  VERINA43MaxGetD
    (
      VERINA43Products
        ( VERINA43NonEmptySubsets A )
    )
) $.

${
  $d i j k p A B C $.

  verina43-post-mask-word-graph-definition $a |- (
    VERINA43PostMaskWordGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ( 0 ..^ ( 2 ^ ( # ` A ) ) )
      )
      /\
      C e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` C )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              ( p ` i ) < ( # ` A )
              /\
              ( C ` i ) = ( A ` ( p ` i ) )
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            A. j e. ( 0 ..^ ( # ` p ) )
              (
                i < j
                ->
                ( p ` i ) < ( p ` j )
              )
          /\
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              (
                VERINA43BitSet
                  B
                  ( ( ( # ` A ) - 1 ) - k )
              )
              <->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = k
            )
        )
      )
  ) $.
$}

${
  $d r A B $.

  verina43-sublists-graph-definition $a |- (
    VERINA43SublistsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    (
      ( # ` B ) = ( 2 ^ ( # ` A ) )
      /\
      A. r e. ( 0 ..^ ( # ` B ) )
        (
          VERINA43PostMaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina43-sublists-definition $a |- (
    VERINA43Sublists A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA43SublistsGraph A y )
  ) $.
$}

${
  $d j A B $.

  verina43-nonempty-sublists-graph-definition $a |- (
    VERINA43NonEmptySublistsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    (
      ( # ` B ) = ( ( # ` ( VERINA43Sublists A ) ) - 1 )
      /\
      A. j e. ( 0 ..^ ( # ` B ) )
        (
          B ` j
        ) = (
          ( VERINA43Sublists A ) ` ( j + 1 )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina43-nonempty-sublists-definition $a |- (
    VERINA43NonEmptySublists A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA43NonEmptySublistsGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina43-post-products-graph-definition $a |- (
    VERINA43PostProductsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = (
        # ` ( VERINA43NonEmptySublists A )
      )
      /\
      A. k e. ( 0 ..^ ( # ` B ) )
        (
          B ` k
        ) = (
          VERINA43Product
            ( ( VERINA43NonEmptySublists A ) ` k )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina43-post-products-definition $a |- (
    VERINA43PostProducts A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA43PostProductsGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina43-postcondition-definition $a |- (
    VERINA43Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      B e. ran ( VERINA43PostProducts A )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA43PostProducts A ) )
      )
        (
          ( VERINA43PostProducts A ) ` k
        ) <_ B
    )
  ) $.
$}

verina-advanced-43-max-strength $a |- A. w e. Word ZZ
  (
    ( VERINA43Pre w )
    ->
    (
      VERINA43Post
        w
        ( VERINA43MaxStrength w )
    )
  )
$.
