$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/equality_up_to_spaces_Top_compare_up_to_spacesqtvc: the
  equality-up-to-spaces comparison verification condition initializes and
  preserves a suffix invariant while skipping spaces, comparing characters,
  and detecting unequal exhaustion. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  C is the arbitrary nonempty character carrier, B is the distinguished
  space character, and D is the source's chosen default inhabitant. Word C
  is exactly the type of arbitrary finite character lists. Booleans are the
  two-element carrier 2, with false = 0 and true = 1.

  E is the source Boolean character-equality function, uncurried to a total
  function on C X. C; the displayed specification is exactly the source
  equality specification under the standard currying bijection. F is the
  total remove_spaces function. NTP4VCRemoveLaw retains its complete recursive
  source equation. The unused source type char_string does not occur in the
  verification condition or in either defining axiom.

  NTP4VCToNat is Int.toNat, NTP4VCAt is totalized list lookup, and NTP4VCDrop
  is the reindexed suffix produced by List.drop. NTP4VCInvariant,
  NTP4VCAdvanceX, NTP4VCAdvanceY, and NTP4VCAdvanceBoth directly factor the
  source bounds, decreasing variants, and remove_spaces equivalences.
  NTP4VCObserve retains each quantified Boolean result together with the
  repeated equality-specification fact. NTP4VCCompare and NTP4VCStep expand
  proposition-valued conditionals into their equivalent exhaustive guarded
  implications while preserving every Boolean and integer quantifier at its
  source scope.

  The final $a declaration is Metamath's native unproved statement encoding.
  Every other $a declaration is syntax or a faithful definition; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCDrop NTP4VCEq NTP4VCRemoveLaw
  NTP4VCInvariant NTP4VCObserve
  NTP4VCAdvanceX NTP4VCAdvanceY NTP4VCAdvanceBoth
  NTP4VCCompare NTP4VCStep
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B C ) $.
ntp4vc-drop-syntax
  $a class ( NTP4VCDrop A B ) $.
ntp4vc-eq-syntax
  $a class ( NTP4VCEq A B C ) $.
ntp4vc-remove-law-syntax
  $a wff ( NTP4VCRemoveLaw A B C D E ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E ) $.
ntp4vc-observe-syntax
  $a wff ( NTP4VCObserve A B C D E F ) $.
ntp4vc-advance-x-syntax
  $a wff ( NTP4VCAdvanceX A B C D E ) $.
ntp4vc-advance-y-syntax
  $a wff ( NTP4VCAdvanceY A B C D E ) $.
ntp4vc-advance-both-syntax
  $a wff ( NTP4VCAdvanceBoth A B C D E ) $.
ntp4vc-compare-syntax
  $a wff ( NTP4VCCompare A B C D E F G ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G H ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 < A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

${
  $d k A B $.

  ntp4vc-drop-definition $a |- (
    NTP4VCDrop A B
  ) = (
    k e. ( 0 ..^ ( ( # ` A ) - ( NTP4VCToNat B ) ) )
    |-> ( A ` ( k + ( NTP4VCToNat B ) ) )
  ) $.
$}

ntp4vc-eq-definition $a |- (
  NTP4VCEq A B C
) = (
  A ` <. B , C >.
) $.

${
  $d s A B C D E $.

  $(
    A is the character carrier, B is space, C is the default inhabitant,
    D is Boolean equality, and E is remove_spaces.
  $)
  ntp4vc-remove-law-definition $a |- (
    NTP4VCRemoveLaw A B C D E
  ) <-> (
    A. s e. Word A
      (
        ( E ` s )
        =
        if (
          ( # ` s ) = 0 ,
          s ,
          if (
            (
              NTP4VCEq
                D
                ( NTP4VCAt s 0 C )
                B
            ) = 1 ,
            ( E ` ( NTP4VCDrop s 1 ) ) ,
            (
              <" ( NTP4VCAt s 0 C ) ">
              ++
              ( E ` ( NTP4VCDrop s 1 ) )
            )
          )
        )
      )
  ) $.
$}

ntp4vc-invariant-definition $a |- (
  NTP4VCInvariant A B C D E
) <-> (
  (
    0 <_ D
    /\
    D <_ ( # ` A )
  )
  /\
  (
    (
      0 <_ E
      /\
      E <_ ( # ` B )
    )
    /\
    (
      (
        ( C ` A ) = ( C ` B )
      )
      <->
      (
        ( C ` ( NTP4VCDrop A D ) )
        =
        ( C ` ( NTP4VCDrop B E ) )
      )
    )
  )
) $.

ntp4vc-observe-definition $a |- (
  NTP4VCObserve A B C D E F
) <-> (
  (
    B < ( # ` A )
    /\
    (
      F = (
        NTP4VCEq
          E
          ( NTP4VCAt A B D )
          C
      )
      /\
      (
        F = 1
        <->
        ( NTP4VCAt A B D ) = C
      )
    )
  )
  \/
  (
    -. B < ( # ` A )
    /\
    F = 0
  )
) $.

ntp4vc-advance-x-definition $a |- (
  NTP4VCAdvanceX A B C D E
) <-> (
  (
    0 <_ (
      (
        ( ( # ` A ) - D )
        +
        ( # ` B )
      )
      -
      E
    )
    /\
    (
      (
        (
          ( ( # ` A ) - ( D + 1 ) )
          +
          ( # ` B )
        )
        -
        E
      )
      <
      (
        (
          ( ( # ` A ) - D )
          +
          ( # ` B )
        )
        -
        E
      )
    )
  )
  /\
  (
    NTP4VCInvariant
      A B C ( D + 1 ) E
  )
) $.

ntp4vc-advance-y-definition $a |- (
  NTP4VCAdvanceY A B C D E
) <-> (
  (
    0 <_ (
      (
        ( ( # ` A ) - D )
        +
        ( # ` B )
      )
      -
      E
    )
    /\
    (
      (
        (
          ( ( # ` A ) - D )
          +
          ( # ` B )
        )
        -
        ( E + 1 )
      )
      <
      (
        (
          ( ( # ` A ) - D )
          +
          ( # ` B )
        )
        -
        E
      )
    )
  )
  /\
  (
    NTP4VCInvariant
      A B C D ( E + 1 )
  )
) $.

ntp4vc-advance-both-definition $a |- (
  NTP4VCAdvanceBoth A B C D E
) <-> (
  (
    0 <_ (
      (
        ( ( # ` A ) - D )
        +
        ( # ` B )
      )
      -
      E
    )
    /\
    (
      (
        (
          ( ( # ` A ) - ( D + 1 ) )
          +
          ( # ` B )
        )
        -
        ( E + 1 )
      )
      <
      (
        (
          ( ( # ` A ) - D )
          +
          ( # ` B )
        )
        -
        E
      )
    )
  )
  /\
  (
    NTP4VCInvariant
      A B C ( D + 1 ) ( E + 1 )
  )
) $.

${
  $d A B C D E F G $.

  $(
    A and B are x and y, C is the default character, D is Boolean
    equality, E is remove_spaces, and F and G are i and j.
  $)
  ntp4vc-compare-definition $a |- (
    NTP4VCCompare A B C D E F G
  ) <-> (
    (
      (
        (
          NTP4VCEq
            D
            ( NTP4VCAt A F C )
            ( NTP4VCAt B G C )
        ) = 1
      )
      <->
      (
        ( NTP4VCAt A F C )
        =
        ( NTP4VCAt B G C )
      )
    )
    ->
    (
      (
        (
          NTP4VCEq
            D
            ( NTP4VCAt A F C )
            ( NTP4VCAt B G C )
        ) =/= 1
        ->
        -. ( E ` A ) = ( E ` B )
      )
      /\
      (
        (
          NTP4VCEq
            D
            ( NTP4VCAt A F C )
            ( NTP4VCAt B G C )
        ) = 1
        ->
        (
          NTP4VCAdvanceBoth
            A B E F G
        )
      )
    )
  ) $.
$}

${
  $d r s t u A B C D E F G H $.

  $(
    A and B are x and y, C is space, D is the default character, E is
    Boolean equality, F is remove_spaces, and G and H are i and j.
    The bound variables r, s, t, and u are source o1, o2, o3, and o4.
  $)
  ntp4vc-step-definition $a |- (
    NTP4VCStep A B C D E F G H
  ) <-> (
    A. r e. 2
      (
        r = if (
          G < ( # ` A ) ,
          1 ,
          if (
            H < ( # ` B ) ,
            1 ,
            0
          )
        )
        ->
        (
          (
            r = 1
            ->
            A. s e. 2
              (
                ( NTP4VCObserve A G C D E s )
                ->
                (
                  (
                    s = 1
                    ->
                    (
                      NTP4VCAdvanceX
                        A B F G H
                    )
                  )
                  /\
                  (
                    s =/= 1
                    ->
                    A. t e. 2
                      (
                        ( NTP4VCObserve B H C D E t )
                        ->
                        (
                          (
                            t = 1
                            ->
                            (
                              NTP4VCAdvanceY
                                A B F G H
                            )
                          )
                          /\
                          (
                            t =/= 1
                            ->
                            A. u e. 2
                              (
                                u = if (
                                  G = ( # ` A ) ,
                                  1 ,
                                  if (
                                    H = ( # ` B ) ,
                                    1 ,
                                    0
                                  )
                                )
                                ->
                                (
                                  (
                                    u = 1
                                    ->
                                    -. ( F ` A ) = ( F ` B )
                                  )
                                  /\
                                  (
                                    u =/= 1
                                    ->
                                    (
                                      NTP4VCCompare
                                        A B D E F G H
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
          /\
          (
            r =/= 1
            ->
            ( F ` A ) = ( F ` B )
          )
        )
      )
  ) $.
$}

${
  $d i j r s t u v w A B C D E F G $.

  $(
    Source context: A is char, B is space, C is the default inhabitant,
    D is eq, E is remove_spaces, and F and G are x and y.
  $)
  ntp4vc-space-character
    $e |- B e. A $.
  ntp4vc-default-character
    $e |- C e. A $.

  ntp4vc-eq-function
    $e |- D e. ( 2 ^m ( A X. A ) ) $.

  ntp4vc-eq-specification
    $e |- A. v e. A A. w e. A
      (
        (
          NTP4VCEq D v w
        ) = 1
        <->
        v = w
      ) $.

  ntp4vc-remove-function
    $e |- E e. ( ( Word A ) ^m ( Word A ) ) $.

  ntp4vc-remove-definition
    $e |- ( NTP4VCRemoveLaw A B C D E ) $.

  ntp4vc-x-list
    $e |- F e. Word A $.
  ntp4vc-y-list
    $e |- G e. Word A $.

  ntp4vc-pearl-equality-up-to-spaces-top-compare-up-to-spaces-vc
    $a |- (
      ( NTP4VCInvariant F G E 0 0 )
      /\
      A. j e. ZZ
        A. i e. ZZ
          (
            ( NTP4VCInvariant F G E i j )
            ->
            (
              NTP4VCStep
                F G B C D E i j
            )
          )
    ) $.
$}
