$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/list_removal_Top_remove1qtvc: the linked-list removal verification
  condition initializes and preserves traversal invariants, then bypasses
  the distinguished entry at the head or after its predecessor. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  F is the arbitrary inhabited source carrier loc; E, C, and D are null,
  head, and entry. B is the total next-location function mem1. A represents
  the proposition-valued source operation list extensionally as a relation
  on next functions, start locations, integer lengths, and end locations.
  Its displayed recursion law is exactly list'def for every nonnegative
  integer length. The unused source carrier mem is omitted because it occurs
  in neither the theorem parameters, assumptions, nor conclusion.

  NTP4VCUpdate is exact total function update on F. Source let-bindings are
  eliminated by definitional substitution. Proposition-valued conditionals
  are expanded into exhaustive guarded implications, preserving their
  internal quantifier scopes. All lengths retain the full unbounded integer
  domain ZZ, and all locations and next functions retain their arbitrary
  source domains.

  Splitting the theorem's typed parameters, global source axioms, and four
  explicit premises into scoped essential hypotheses is bidirectionally
  equivalent to the source curried theorem. Every auxiliary $a declaration
  below is syntax or an explicit faithful definition. The final $a
  declaration is Metamath's native unproved statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCList NTP4VCUpdate NTP4VCInitial NTP4VCLoopState
  NTP4VCAdvance NTP4VCRemoveHead NTP4VCRemoveAfter
  NTP4VCStep NTP4VCRemove1VC
$.

ntp4vc-list-syntax
  $a wff ( NTP4VCList A B C D E ) $.
ntp4vc-update-syntax
  $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C D E F G ) $.
ntp4vc-loop-state-syntax
  $a wff ( NTP4VCLoopState A B C D E F G H I J ) $.
ntp4vc-advance-syntax
  $a wff ( NTP4VCAdvance A B C D E F G H I J ) $.
ntp4vc-remove-head-syntax
  $a wff ( NTP4VCRemoveHead A B C D E F G H I J ) $.
ntp4vc-remove-after-syntax
  $a wff ( NTP4VCRemoveAfter A B C D E F G H I J K ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G H I J K ) $.
ntp4vc-remove1-vc-syntax
  $a wff ( NTP4VCRemove1VC A B C D E F G H ) $.

ntp4vc-list-definition $a |- (
  NTP4VCList A B C D E
) <-> (
  <. <. <. B , C >. , D >. , E >. e. A
) $.

${
  $d x A B C D $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C D
  ) = (
    x e. D |->
      if ( x = B , C , ( A ` x ) )
  ) $.
$}

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A B C D E F G
) <-> (
  (
    0 < 1
    /\
    1 <_ F
  )
  /\
  (
    ( NTP4VCList A B C 1 ( B ` C ) )
    /\
    (
      ( B ` C ) =/= E
      /\
      (
        ( NTP4VCList A B ( B ` C ) ( F - 1 ) D )
        /\
        ( NTP4VCList A B D G E )
      )
    )
  )
) $.

ntp4vc-loop-state-definition $a |- (
  NTP4VCLoopState A B C D E F G H I J
) <-> (
  (
    0 < H
    /\
    H <_ F
  )
  /\
  (
    ( NTP4VCList A B C H I )
    /\
    (
      I =/= E
      /\
      (
        (
          J = E
          ->
          H = 1
        )
        /\
        (
          (
            J =/= E
            ->
            ( B ` J ) = I
          )
          /\
          (
            (
              J =/= E
              ->
              ( NTP4VCList A B C ( H - 1 ) J )
            )
            /\
            (
              ( NTP4VCList A B I ( F - H ) D )
              /\
              ( NTP4VCList A B D G E )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-advance-definition $a |- (
  NTP4VCAdvance A B C D E F G H I J
) <-> (
  J =/= E
  /\
  (
    (
      0 <_ ( G - I )
      /\
      ( G - ( I + 1 ) ) < ( G - I )
    )
    /\
    (
      (
        0 < ( I + 1 )
        /\
        ( I + 1 ) <_ G
      )
      /\
      (
        ( NTP4VCList A B C ( I + 1 ) ( B ` J ) )
        /\
        (
          ( B ` J ) =/= E
          /\
          (
            (
              J = E
              ->
              ( I + 1 ) = 1
            )
            /\
            (
              (
                J =/= E
                ->
                T.
              )
              /\
              (
                (
                  J =/= E
                  ->
                  ( NTP4VCList A B C ( ( I + 1 ) - 1 ) J )
                )
                /\
                (
                  ( NTP4VCList
                    A B ( B ` J ) ( G - ( I + 1 ) ) D
                  )
                  /\
                  ( NTP4VCList A B D H E )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-remove-head-definition $a |- (
  NTP4VCRemoveHead A B C D E F G H I J
) <-> (
  J =/= E
  /\
  (
    C =/= E
    /\
    ( NTP4VCList
      A
      ( NTP4VCUpdate B C ( B ` J ) F )
      C
      ( ( G + H ) - 1 )
      E
    )
  )
) $.

ntp4vc-remove-after-definition $a |- (
  NTP4VCRemoveAfter A B C D E F G H I J K
) <-> (
  J =/= E
  /\
  (
    K =/= E
    /\
    ( NTP4VCList
      A
      ( NTP4VCUpdate B K ( B ` J ) F )
      C
      ( ( G + H ) - 1 )
      E
    )
  )
) $.

ntp4vc-step-definition $a |- (
  NTP4VCStep A B C D E F G H I J K
) <-> (
  (
    J =/= D
    ->
    ( NTP4VCAdvance A B C D E F G H I J )
  )
  /\
  (
    J = D
    ->
    (
      (
        K = E
        ->
        ( NTP4VCRemoveHead A B C D E F G H I J )
      )
      /\
      (
        K =/= E
        ->
        ( NTP4VCRemoveAfter A B C D E F G H I J K )
      )
    )
  )
) $.

${
  $d i j k A B C D E F G H $.

  ntp4vc-remove1-vc-definition $a |- (
    NTP4VCRemove1VC A B C D E F G H
  ) <-> (
    C =/= E
    /\
    (
      ( NTP4VCInitial A B C D E G H )
      /\
      A. i e. ZZ A. j e. F A. k e. F
        (
          ( NTP4VCLoopState A B C D E G H i j k )
          ->
          ( NTP4VCStep A B C D E F G H i j k )
        )
    )
  ) $.
$}

${
  $d i j k l m n x y
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carrier, constants, predicate, and theorem parameters:
     F=loc, E=null, C=head, D=entry, A=list, B=mem1, G=n1, H=n2. $)

  ntp4vc-location-carrier-nonempty $e |- F =/= (/) $.
  ntp4vc-null-location $e |- E e. F $.
  ntp4vc-head-location $e |- C e. F $.
  ntp4vc-entry-location $e |- D e. F $.

  ntp4vc-head-is-not-null $e |- C =/= E $.
  ntp4vc-entry-is-not-null $e |- D =/= E $.
  ntp4vc-head-is-not-entry $e |- C =/= D $.

  ntp4vc-list-relation $e |- A C_
    (
      (
        (
          ( F ^m F )
          X.
          F
        )
        X.
        ZZ
      )
      X.
      F
    ) $.

  ntp4vc-list-recursion $e |- A. m e. ( F ^m F )
    A. x e. F A. n e. ZZ A. y e. F
      (
        0 <_ n
        ->
        (
          (
            n = 0
            ->
            (
              ( NTP4VCList A m x n y )
              <->
              x = y
            )
          )
          /\
          (
            n =/= 0
            ->
            (
              ( NTP4VCList A m x n y )
              <->
              (
                x =/= E
                /\
                ( NTP4VCList A m ( m ` x ) ( n - 1 ) y )
              )
            )
          )
        )
      ) $.

  ntp4vc-n1-integer $e |- G e. ZZ $.
  ntp4vc-n2-integer $e |- H e. ZZ $.
  ntp4vc-mem1-function $e |- B e. ( F ^m F ) $.

  ntp4vc-fact0 $e |- 0 < G $.
  ntp4vc-fact1 $e |- 0 < H $.
  ntp4vc-fact2 $e |- ( NTP4VCList A B C G D ) $.
  ntp4vc-fact3 $e |- ( NTP4VCList A B D H E ) $.

  ntp4vc-pearl-list-removal-top-remove1-vc
    $a |- ( NTP4VCRemove1VC A B C D E F G H ) $.
$}
