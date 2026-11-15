$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/register_allocation_FiniteNumberOfRegisters_compileqtvc: the
  verification condition for compiling expression trees with at least two
  integer-indexed registers, using direct allocation or stack spilling while
  preserving the double-weakest-precondition correctness specification.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary inhabited Why3 address type is the nonempty set A. The
  expression carrier is the least set closed under the three tagged source
  constructors; its closure, exhaustiveness, and structural-induction
  hypotheses below give the exact finite inductive type. Instructions, states,
  memories, register files, stacks, and finite instruction lists use direct
  SetMM encodings. The evaluation, register update, instruction execution,
  and list execution equations reproduce every source defining equation.

  Bool-valued state predicates and binary postconditions are represented by
  subsets of their input carriers. Predicate transformers are subsets of
  P(State) x State, the characteristic-set representation of the exact
  two-element Boolean function space. NTP4VCIdentity, NTP4VCToWP,
  NTP4VCConsTrans, and NTP4VCComposeTrans are the source identity,
  weakest-precondition conversion, instruction precomposition, and rcompose
  operations under this bijection.

  The source expression match is expanded as the disjoint union of its three
  constructor cases, and each proposition-valued conditional is expanded as
  its two complementary guarded cases. NTP4VCBranches preserves every
  universally quantified VC obligation. NTP4VCBuild preserves every internal
  existential witness for the generated weak and Hoare code records. All
  registers and values range over the full integer class ZZ. The final $a is
  Metamath's native unproved statement encoding; there is no $p declaration.
$)

$c
  NTP4VCEvar NTP4VCEneg NTP4VCEadd
  NTP4VCState NTP4VCInstr
  NTP4VCIload NTP4VCIneg NTP4VCIadd NTP4VCIpush NTP4VCIpop
  NTP4VCUpdate NTP4VCExprPost NTP4VCPostAt
  NTP4VCWCode NTP4VCHCode NTP4VCWCodeOk NTP4VCHCodeOk
  NTP4VCTransAt NTP4VCIdentity NTP4VCToWP
  NTP4VCConsTrans NTP4VCComposeTrans
  NTP4VCSubexpr NTP4VCInRange
  NTP4VCVarReq NTP4VCNegReq NTP4VCAddDirectReq NTP4VCAddSpillReq
  NTP4VCBuildVar NTP4VCBuildNeg
  NTP4VCBuildAddDirect NTP4VCBuildAddSpill
  NTP4VCBranches NTP4VCBuild
$.

ntp4vc-evar-syntax $a class ( NTP4VCEvar A ) $.
ntp4vc-eneg-syntax $a class ( NTP4VCEneg A ) $.
ntp4vc-eadd-syntax $a class ( NTP4VCEadd A B ) $.

ntp4vc-state-syntax $a class ( NTP4VCState A ) $.
ntp4vc-instr-syntax $a class ( NTP4VCInstr A ) $.
ntp4vc-iload-syntax $a class ( NTP4VCIload A B ) $.
ntp4vc-ineg-syntax $a class ( NTP4VCIneg A ) $.
ntp4vc-iadd-syntax $a class ( NTP4VCIadd A B ) $.
ntp4vc-ipush-syntax $a class ( NTP4VCIpush A ) $.
ntp4vc-ipop-syntax $a class ( NTP4VCIpop A ) $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-expr-post-syntax $a class ( NTP4VCExprPost A B C D ) $.
ntp4vc-post-at-syntax $a class ( NTP4VCPostAt A B C ) $.

ntp4vc-wcode-syntax $a class ( NTP4VCWCode A ) $.
ntp4vc-hcode-syntax $a class ( NTP4VCHCode A ) $.
ntp4vc-wcode-ok-syntax $a wff ( NTP4VCWCodeOk A B C ) $.
ntp4vc-hcode-ok-syntax $a wff ( NTP4VCHCodeOk A B C ) $.

ntp4vc-trans-at-syntax $a class ( NTP4VCTransAt A B C ) $.
ntp4vc-identity-syntax $a class ( NTP4VCIdentity A ) $.
ntp4vc-to-wp-syntax $a class ( NTP4VCToWP A B ) $.
ntp4vc-cons-trans-syntax $a class ( NTP4VCConsTrans A B C D ) $.
ntp4vc-compose-trans-syntax $a class ( NTP4VCComposeTrans A B C ) $.

ntp4vc-subexpr-syntax $a wff ( NTP4VCSubexpr A B ) $.
ntp4vc-in-range-syntax $a wff ( NTP4VCInRange A B ) $.

ntp4vc-var-req-syntax $a wff ( NTP4VCVarReq A B ) $.
ntp4vc-neg-req-syntax
  $a wff ( NTP4VCNegReq A B C D E F G H ) $.
ntp4vc-add-direct-req-syntax
  $a wff ( NTP4VCAddDirectReq A B C D E F G H I ) $.
ntp4vc-add-spill-req-syntax
  $a wff ( NTP4VCAddSpillReq A B C D E F G H I ) $.

ntp4vc-build-var-syntax
  $a wff ( NTP4VCBuildVar A B C D E F ) $.
ntp4vc-build-neg-syntax
  $a wff ( NTP4VCBuildNeg A B C D E F G ) $.
ntp4vc-build-add-direct-syntax
  $a wff ( NTP4VCBuildAddDirect A B C D E F G H I ) $.
ntp4vc-build-add-spill-syntax
  $a wff ( NTP4VCBuildAddSpill A B C D E F G H I ) $.
ntp4vc-branches-syntax
  $a wff ( NTP4VCBranches A B C D E F G H ) $.
ntp4vc-build-syntax
  $a wff ( NTP4VCBuild A B C D E F G H I ) $.

ntp4vc-evar-definition $a |- (
  NTP4VCEvar A
) = <. 0 , A >. $.

ntp4vc-eneg-definition $a |- (
  NTP4VCEneg A
) = <. 1 , A >. $.

ntp4vc-eadd-definition $a |- (
  NTP4VCEadd A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-state-definition $a |- (
  NTP4VCState A
) = (
  ( ZZ ^m A )
  X.
  ( ( ZZ ^m ZZ ) X. Word ZZ )
) $.

ntp4vc-iload-definition $a |- (
  NTP4VCIload A B
) = <. 0 , <. A , B >. >. $.

ntp4vc-ineg-definition $a |- (
  NTP4VCIneg A
) = <. 1 , A >. $.

ntp4vc-iadd-definition $a |- (
  NTP4VCIadd A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-ipush-definition $a |- (
  NTP4VCIpush A
) = <. 3 , A >. $.

ntp4vc-ipop-definition $a |- (
  NTP4VCIpop A
) = <. 4 , A >. $.

ntp4vc-instr-definition $a |- (
  NTP4VCInstr A
) = (
  ( { 0 } X. ( A X. ZZ ) )
  u.
  (
    ( { 1 } X. ZZ )
    u.
    (
      ( { 2 } X. ( ZZ X. ZZ ) )
      u.
      (
        ( { 3 } X. ZZ )
        u.
        ( { 4 } X. ZZ )
      )
    )
  )
) $.

${
  $d z A B C $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C
  ) = (
    z e. ZZ |->
      if ( z = B , C , ( A ` z ) )
  ) $.
$}

${
  $d r z A B C D $.

  ntp4vc-expr-post-definition $a |- (
    NTP4VCExprPost A B C D
  ) = {
    z e. ( ( NTP4VCState A ) X. ( NTP4VCState A ) ) |
      (
        ( 1st ` ( 2nd ` z ) )
        =
        ( 1st ` ( 1st ` z ) )
      )
      /\
      (
        (
          ( 1st ` ( 2nd ` ( 2nd ` z ) ) )
          ` D
        )
        =
        (
          B ` <.
            ( 1st ` ( 1st ` z ) ) ,
            C
          >.
        )
      )
      /\
      (
        ( 2nd ` ( 2nd ` ( 2nd ` z ) ) )
        =
        ( 2nd ` ( 2nd ` ( 1st ` z ) ) )
      )
      /\
      A. r e. ZZ
        (
          r < D
          ->
          (
            (
              ( 1st ` ( 2nd ` ( 2nd ` z ) ) )
              ` r
            )
            =
            (
              ( 1st ` ( 2nd ` ( 1st ` z ) ) )
              ` r
            )
          )
        )
  } $.
$}

${
  $d y A B C $.

  ntp4vc-post-at-definition $a |- (
    NTP4VCPostAt A B C
  ) = {
    y e. ( NTP4VCState A ) |
      <. C , y >. e. B
  } $.
$}

ntp4vc-wcode-definition $a |- (
  NTP4VCWCode A
) = (
  (
    ~P (
      ( ~P ( NTP4VCState A ) )
      X.
      ( NTP4VCState A )
    )
  )
  X.
  Word ( NTP4VCInstr A )
) $.

ntp4vc-hcode-definition $a |- (
  NTP4VCHCode A
) = (
  Word ( NTP4VCInstr A )
  X.
  ~P (
    ( NTP4VCState A )
    X.
    ( NTP4VCState A )
  )
) $.

${
  $d q s A B C $.

  ntp4vc-wcode-ok-definition $a |- (
    NTP4VCWCodeOk A B C
  ) <-> (
    A. q e. ~P ( NTP4VCState A )
      A. s e. ( NTP4VCState A )
        (
          <. q , s >. e. ( 1st ` C )
          ->
          (
            B ` <. ( 2nd ` C ) , s >.
          ) e. q
        )
  ) $.
$}

${
  $d s A B C $.

  ntp4vc-hcode-ok-definition $a |- (
    NTP4VCHCodeOk A B C
  ) <-> (
    A. s e. ( NTP4VCState A )
      <.
        s ,
        ( B ` <. ( 1st ` C ) , s >. )
      >. e. ( 2nd ` C )
  ) $.
$}

${
  $d s A B C $.

  ntp4vc-trans-at-definition $a |- (
    NTP4VCTransAt A B C
  ) = {
    s e. ( NTP4VCState A ) |
      <. C , s >. e. B
  } $.
$}

${
  $d z A $.

  ntp4vc-identity-definition $a |- (
    NTP4VCIdentity A
  ) = {
    z e. (
      ( ~P ( NTP4VCState A ) )
      X.
      ( NTP4VCState A )
    ) |
      ( 2nd ` z ) e. ( 1st ` z )
  } $.
$}

${
  $d s z A B $.

  ntp4vc-to-wp-definition $a |- (
    NTP4VCToWP A B
  ) = {
    z e. (
      ( ~P ( NTP4VCState A ) )
      X.
      ( NTP4VCState A )
    ) |
      A. s e. ( NTP4VCState A )
        (
          <. ( 2nd ` z ) , s >. e. B
          ->
          s e. ( 1st ` z )
        )
  } $.
$}

${
  $d z A B C D $.

  ntp4vc-cons-trans-definition $a |- (
    NTP4VCConsTrans A B C D
  ) = {
    z e. (
      ( ~P ( NTP4VCState A ) )
      X.
      ( NTP4VCState A )
    ) |
      <.
        ( 1st ` z ) ,
        ( B ` <. D , ( 2nd ` z ) >. )
      >. e. C
  } $.
$}

${
  $d z A B C $.

  ntp4vc-compose-trans-definition $a |- (
    NTP4VCComposeTrans A B C
  ) = {
    z e. (
      ( ~P ( NTP4VCState A ) )
      X.
      ( NTP4VCState A )
    ) |
      <.
        ( NTP4VCTransAt A B ( 1st ` z ) ) ,
        ( 2nd ` z )
      >. e. C
  } $.
$}

${
  $d a b A B $.

  ntp4vc-subexpr-definition $a |- (
    NTP4VCSubexpr A B
  ) <-> (
    E. a
      (
        A = ( NTP4VCEneg a )
        /\
        a = B
      )
    \/
    E. a E. b
      (
        A = ( NTP4VCEadd a b )
        /\
        (
          a = B
          \/
          b = B
        )
      )
  ) $.
$}

ntp4vc-in-range-definition $a |- (
  NTP4VCInRange A B
) <-> (
  0 <_ B
  /\
  B < A
) $.

${
  $d o A B $.

  ntp4vc-var-req-definition $a |- (
    NTP4VCVarReq A B
  ) <-> (
    A. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A B o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        ->
        ( NTP4VCWCodeOk A B o )
      )
  ) $.
$}

${
  $d o p q t A B C D E F G H $.

  ntp4vc-neg-req-definition $a |- (
    NTP4VCNegReq A B C D E F G H
  ) <-> (
    A. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A C o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        ->
        (
          ( NTP4VCWCodeOk A C o )
          /\
          A. p e. ( NTP4VCWCode A )
            (
              (
                ( NTP4VCWCodeOk A C p )
                /\
                ( 1st ` p )
                =
                (
                  NTP4VCConsTrans
                    A B ( 1st ` o ) ( NTP4VCIneg F )
                )
              )
              ->
              (
                (
                  ( NTP4VCSubexpr G H )
                  /\
                  ( NTP4VCInRange E F )
                )
                /\
                A. q e. ( NTP4VCHCode A )
                  (
                    (
                      ( NTP4VCHCodeOk A C q )
                      /\
                      ( 2nd ` q )
                      =
                      ( NTP4VCExprPost A D H F )
                    )
                    ->
                    (
                      ( NTP4VCHCodeOk A C q )
                      /\
                      A. t e. ( NTP4VCWCode A )
                        (
                          (
                            ( NTP4VCWCodeOk A C t )
                            /\
                            ( 1st ` t )
                            =
                            ( NTP4VCToWP A ( 2nd ` q ) )
                          )
                          ->
                          (
                            ( NTP4VCWCodeOk A C t )
                            /\
                            ( NTP4VCWCodeOk A C p )
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
  $d o p q s t u v w A B C D E F G H I $.

  ntp4vc-add-direct-req-definition $a |- (
    NTP4VCAddDirectReq A B C D E F G H I
  ) <-> (
    A. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A C o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        ->
        (
          ( NTP4VCWCodeOk A C o )
          /\
          A. p e. ( NTP4VCWCode A )
            (
              (
                ( NTP4VCWCodeOk A C p )
                /\
                ( 1st ` p )
                =
                (
                  NTP4VCConsTrans A B ( 1st ` o )
                    ( NTP4VCIadd ( F + 1 ) F )
                )
              )
              ->
              (
                (
                  ( NTP4VCSubexpr G I )
                  /\
                  ( NTP4VCInRange E ( F + 1 ) )
                )
                /\
                A. q e. ( NTP4VCHCode A )
                  (
                    (
                      ( NTP4VCHCodeOk A C q )
                      /\
                      ( 2nd ` q )
                      =
                      ( NTP4VCExprPost A D I ( F + 1 ) )
                    )
                    ->
                    (
                      ( NTP4VCHCodeOk A C q )
                      /\
                      A. s e. ( NTP4VCWCode A )
                        (
                          (
                            ( NTP4VCWCodeOk A C s )
                            /\
                            ( 1st ` s )
                            =
                            ( NTP4VCToWP A ( 2nd ` q ) )
                          )
                          ->
                          (
                            (
                              ( NTP4VCSubexpr G H )
                              /\
                              ( NTP4VCInRange E F )
                            )
                            /\
                            A. t e. ( NTP4VCHCode A )
                              (
                                (
                                  ( NTP4VCHCodeOk A C t )
                                  /\
                                  ( 2nd ` t )
                                  =
                                  ( NTP4VCExprPost A D H F )
                                )
                                ->
                                (
                                  ( NTP4VCHCodeOk A C t )
                                  /\
                                  A. u e. ( NTP4VCWCode A )
                                    (
                                      (
                                        ( NTP4VCWCodeOk A C u )
                                        /\
                                        ( 1st ` u )
                                        =
                                        ( NTP4VCToWP A ( 2nd ` t ) )
                                      )
                                      ->
                                      (
                                        (
                                          ( NTP4VCWCodeOk A C u )
                                          /\
                                          ( NTP4VCWCodeOk A C s )
                                        )
                                        /\
                                        A. v e. ( NTP4VCWCode A )
                                          (
                                            (
                                              ( NTP4VCWCodeOk A C v )
                                              /\
                                              ( 1st ` v )
                                              =
                                              (
                                                NTP4VCComposeTrans
                                                  A
                                                  ( 1st ` s )
                                                  ( 1st ` u )
                                              )
                                            )
                                            ->
                                            (
                                              ( NTP4VCWCodeOk A C v )
                                              /\
                                              ( NTP4VCWCodeOk A C p )
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
        )
      )
  ) $.
$}

${
  $d o p q s t u v w x y A B C D E F G H I $.

  ntp4vc-add-spill-req-definition $a |- (
    NTP4VCAddSpillReq A B C D E F G H I
  ) <-> (
    A. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A C o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        ->
        (
          ( NTP4VCWCodeOk A C o )
          /\
          A. p e. ( NTP4VCWCode A )
            (
              (
                ( NTP4VCWCodeOk A C p )
                /\
                ( 1st ` p )
                =
                (
                  NTP4VCConsTrans A B ( 1st ` o )
                    ( NTP4VCIpop ( E - 2 ) )
                )
              )
              ->
              (
                ( NTP4VCWCodeOk A C p )
                /\
                A. q e. ( NTP4VCWCode A )
                  (
                    (
                      ( NTP4VCWCodeOk A C q )
                      /\
                      ( 1st ` q )
                      =
                      (
                        NTP4VCConsTrans A B ( 1st ` p )
                          (
                            NTP4VCIadd
                              ( E - 2 )
                              ( E - 1 )
                          )
                      )
                    )
                    ->
                    (
                      (
                        ( NTP4VCSubexpr G I )
                        /\
                        ( NTP4VCInRange E ( E - 1 ) )
                      )
                      /\
                      A. s e. ( NTP4VCHCode A )
                        (
                          (
                            ( NTP4VCHCodeOk A C s )
                            /\
                            ( 2nd ` s )
                            =
                            ( NTP4VCExprPost A D I ( E - 1 ) )
                          )
                          ->
                          (
                            ( NTP4VCHCodeOk A C s )
                            /\
                            A. t e. ( NTP4VCWCode A )
                              (
                                (
                                  ( NTP4VCWCodeOk A C t )
                                  /\
                                  ( 1st ` t )
                                  =
                                  ( NTP4VCToWP A ( 2nd ` s ) )
                                )
                                ->
                                (
                                  (
                                    ( NTP4VCSubexpr G H )
                                    /\
                                    ( NTP4VCInRange E ( E - 2 ) )
                                  )
                                  /\
                                  A. u e. ( NTP4VCHCode A )
                                    (
                                      (
                                        ( NTP4VCHCodeOk A C u )
                                        /\
                                        ( 2nd ` u )
                                        =
                                        (
                                          NTP4VCExprPost
                                            A D H ( E - 2 )
                                        )
                                      )
                                      ->
                                      (
                                        ( NTP4VCHCodeOk A C u )
                                        /\
                                        A. v e. ( NTP4VCWCode A )
                                          (
                                            (
                                              ( NTP4VCWCodeOk A C v )
                                              /\
                                              ( 1st ` v )
                                              =
                                              (
                                                NTP4VCToWP
                                                  A ( 2nd ` u )
                                              )
                                            )
                                            ->
                                            (
                                              (
                                                ( NTP4VCWCodeOk A C v )
                                                /\
                                                ( NTP4VCWCodeOk A C t )
                                              )
                                              /\
                                              A. w e. ( NTP4VCWCode A )
                                                (
                                                  (
                                                    (
                                                      NTP4VCWCodeOk A C w
                                                    )
                                                    /\
                                                    ( 1st ` w )
                                                    =
                                                    (
                                                      NTP4VCComposeTrans
                                                        A
                                                        ( 1st ` t )
                                                        ( 1st ` v )
                                                    )
                                                  )
                                                  ->
                                                  (
                                                    (
                                                      NTP4VCWCodeOk A C w
                                                    )
                                                    /\
                                                    (
                                                      NTP4VCWCodeOk A C q
                                                    )
                                                  )
                                                  /\
                                                  A. x e.
                                                    ( NTP4VCWCode A )
                                                    (
                                                      (
                                                        (
                                                          NTP4VCWCodeOk
                                                            A C x
                                                        )
                                                        /\
                                                        ( 1st ` x )
                                                        =
                                                        (
                                                          NTP4VCComposeTrans
                                                            A
                                                            ( 1st ` q )
                                                            ( 1st ` w )
                                                        )
                                                      )
                                                      ->
                                                      (
                                                        NTP4VCWCodeOk
                                                          A C x
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
                  )
              )
            )
        )
      )
  ) $.
$}

${
  $d o A B C D E F $.

  ntp4vc-build-var-definition $a |- (
    NTP4VCBuildVar A B C D E F
  ) <-> (
    E. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A C o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        /\
        (
          ( NTP4VCWCodeOk A C F )
          /\
          ( 1st ` F )
          =
          (
            NTP4VCConsTrans A B ( 1st ` o )
              ( NTP4VCIload E D )
          )
        )
      )
  ) $.
$}

${
  $d o p q s A B C D E F G $.

  ntp4vc-build-neg-definition $a |- (
    NTP4VCBuildNeg A B C D E F G
  ) <-> (
    E. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A C o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        /\
        E. p e. ( NTP4VCWCode A )
          (
            (
              ( NTP4VCWCodeOk A C p )
              /\
              ( 1st ` p )
              =
              (
                NTP4VCConsTrans A B ( 1st ` o )
                  ( NTP4VCIneg E )
              )
            )
            /\
            E. q e. ( NTP4VCHCode A )
              (
                (
                  ( NTP4VCHCodeOk A C q )
                  /\
                  ( 2nd ` q )
                  =
                  ( NTP4VCExprPost A D F E )
                )
                /\
                E. s e. ( NTP4VCWCode A )
                  (
                    (
                      ( NTP4VCWCodeOk A C s )
                      /\
                      ( 1st ` s )
                      =
                      ( NTP4VCToWP A ( 2nd ` q ) )
                    )
                    /\
                    (
                      ( NTP4VCWCodeOk A C G )
                      /\
                      ( 1st ` G )
                      =
                      (
                        NTP4VCComposeTrans A
                          ( 1st ` p ) ( 1st ` s )
                      )
                    )
                  )
              )
          )
      )
  ) $.
$}

${
  $d o p q s t u v A B C D E F G H I $.

  ntp4vc-build-add-direct-definition $a |- (
    NTP4VCBuildAddDirect A B C D E F G H I
  ) <-> (
    E. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A C o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        /\
        E. p e. ( NTP4VCWCode A )
          (
            (
              ( NTP4VCWCodeOk A C p )
              /\
              ( 1st ` p )
              =
              (
                NTP4VCConsTrans A B ( 1st ` o )
                  ( NTP4VCIadd ( F + 1 ) F )
              )
            )
            /\
            E. q e. ( NTP4VCHCode A )
              (
                (
                  ( NTP4VCHCodeOk A C q )
                  /\
                  ( 2nd ` q )
                  =
                  ( NTP4VCExprPost A D H ( F + 1 ) )
                )
                /\
                E. s e. ( NTP4VCWCode A )
                  (
                    (
                      ( NTP4VCWCodeOk A C s )
                      /\
                      ( 1st ` s )
                      =
                      ( NTP4VCToWP A ( 2nd ` q ) )
                    )
                    /\
                    E. t e. ( NTP4VCHCode A )
                      (
                        (
                          ( NTP4VCHCodeOk A C t )
                          /\
                          ( 2nd ` t )
                          =
                          ( NTP4VCExprPost A D G F )
                        )
                        /\
                        E. u e. ( NTP4VCWCode A )
                          (
                            (
                              ( NTP4VCWCodeOk A C u )
                              /\
                              ( 1st ` u )
                              =
                              ( NTP4VCToWP A ( 2nd ` t ) )
                            )
                            /\
                            E. v e. ( NTP4VCWCode A )
                              (
                                (
                                  ( NTP4VCWCodeOk A C v )
                                  /\
                                  ( 1st ` v )
                                  =
                                  (
                                    NTP4VCComposeTrans A
                                      ( 1st ` s ) ( 1st ` u )
                                  )
                                )
                                /\
                                (
                                  ( NTP4VCWCodeOk A C I )
                                  /\
                                  ( 1st ` I )
                                  =
                                  (
                                    NTP4VCComposeTrans A
                                      ( 1st ` p ) ( 1st ` v )
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

${
  $d o p q s t u v w x A B C D E F G H I $.

  ntp4vc-build-add-spill-definition $a |- (
    NTP4VCBuildAddSpill A B C D E F G H I
  ) <-> (
    E. o e. ( NTP4VCWCode A )
      (
        (
          ( NTP4VCWCodeOk A C o )
          /\
          ( 1st ` o ) = ( NTP4VCIdentity A )
        )
        /\
        E. p e. ( NTP4VCWCode A )
          (
            (
              ( NTP4VCWCodeOk A C p )
              /\
              ( 1st ` p )
              =
              (
                NTP4VCConsTrans A B ( 1st ` o )
                  ( NTP4VCIpop ( E - 2 ) )
              )
            )
            /\
            E. q e. ( NTP4VCWCode A )
              (
                (
                  ( NTP4VCWCodeOk A C q )
                  /\
                  ( 1st ` q )
                  =
                  (
                    NTP4VCConsTrans A B ( 1st ` p )
                      (
                        NTP4VCIadd
                          ( E - 2 )
                          ( E - 1 )
                      )
                  )
                )
                /\
                E. s e. ( NTP4VCHCode A )
                  (
                    (
                      ( NTP4VCHCodeOk A C s )
                      /\
                      ( 2nd ` s )
                      =
                      ( NTP4VCExprPost A D H ( E - 1 ) )
                    )
                    /\
                    E. t e. ( NTP4VCWCode A )
                      (
                        (
                          ( NTP4VCWCodeOk A C t )
                          /\
                          ( 1st ` t )
                          =
                          ( NTP4VCToWP A ( 2nd ` s ) )
                        )
                        /\
                        E. u e. ( NTP4VCHCode A )
                          (
                            (
                              ( NTP4VCHCodeOk A C u )
                              /\
                              ( 2nd ` u )
                              =
                              ( NTP4VCExprPost A D G ( E - 2 ) )
                            )
                            /\
                            E. v e. ( NTP4VCWCode A )
                              (
                                (
                                  ( NTP4VCWCodeOk A C v )
                                  /\
                                  ( 1st ` v )
                                  =
                                  ( NTP4VCToWP A ( 2nd ` u ) )
                                )
                                /\
                                E. w e. ( NTP4VCWCode A )
                                  (
                                    (
                                      ( NTP4VCWCodeOk A C w )
                                      /\
                                      ( 1st ` w )
                                      =
                                      (
                                        NTP4VCComposeTrans A
                                          ( 1st ` t ) ( 1st ` v )
                                      )
                                    )
                                    /\
                                    E. x e. ( NTP4VCWCode A )
                                      (
                                        (
                                          ( NTP4VCWCodeOk A C x )
                                          /\
                                          ( 1st ` x )
                                          =
                                          (
                                            NTP4VCComposeTrans A
                                              ( 1st ` q ) ( 1st ` w )
                                          )
                                        )
                                        /\
                                        (
                                          ( NTP4VCWCodeOk A C I )
                                          /\
                                          ( 1st ` I )
                                          =
                                          (
                                            NTP4VCConsTrans A B
                                              ( 1st ` x )
                                              (
                                                NTP4VCIpush
                                                  ( E - 2 )
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
  ) $.
$}

${
  $d a b x A B C D E F G H $.

  ntp4vc-branches-definition $a |- (
    NTP4VCBranches A B C D E F G H
  ) <-> (
    E. x e. A
      (
        H = ( NTP4VCEvar x )
        /\
        ( NTP4VCVarReq A D )
      )
    \/
    E. a e. B
      (
        H = ( NTP4VCEneg a )
        /\
        ( NTP4VCNegReq A C D E F G H a )
      )
    \/
    E. a e. B E. b e. B
      (
        H = ( NTP4VCEadd a b )
        /\
        (
          (
            G < ( F - 1 )
            /\
            (
              NTP4VCAddDirectReq
                A C D E F G H a b
            )
          )
          \/
          (
            -. G < ( F - 1 )
            /\
            (
              NTP4VCAddSpillReq
                A C D E F G H a b
            )
          )
        )
      )
  ) $.
$}

${
  $d a b x A B C D E F G H I $.

  ntp4vc-build-definition $a |- (
    NTP4VCBuild A B C D E F G H I
  ) <-> (
    E. x e. A
      (
        H = ( NTP4VCEvar x )
        /\
        ( NTP4VCBuildVar A C D G x I )
      )
    \/
    E. a e. B
      (
        H = ( NTP4VCEneg a )
        /\
        ( NTP4VCBuildNeg A C D E G a I )
      )
    \/
    E. a e. B E. b e. B
      (
        H = ( NTP4VCEadd a b )
        /\
        (
          (
            G < ( F - 1 )
            /\
            (
              NTP4VCBuildAddDirect
                A C D E F G a b I
            )
          )
          \/
          (
            -. G < ( F - 1 )
            /\
            (
              NTP4VCBuildAddSpill
                A C D E F G a b I
            )
          )
        )
      )
  ) $.
$}

${
  $d a b e i l m o p q r s t u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Arbitrary inhabited source address carrier. $)
  ntp4vc-address-carrier-set $e |- A e. _V $.
  ntp4vc-address-carrier-nonempty $e |- A =/= (/) $.

  $( Exact finite inductive expression carrier. $)
  ntp4vc-expression-carrier-set $e |- B e. _V $.

  ntp4vc-expression-evar-closure $e |- A. x e. A
    ( NTP4VCEvar x ) e. B $.

  ntp4vc-expression-eneg-closure $e |- A. e e. B
    ( NTP4VCEneg e ) e. B $.

  ntp4vc-expression-eadd-closure $e |- A. e e. B A. x e. B
    ( NTP4VCEadd e x ) e. B $.

  ntp4vc-expression-constructor-exhaustive $e |- A. e e. B
    (
      E. x e. A e = ( NTP4VCEvar x )
      \/
      (
        E. x e. B e = ( NTP4VCEneg x )
        \/
        E. x e. B E. y e. B
          e = ( NTP4VCEadd x y )
      )
    ) $.

  ntp4vc-expression-structural-induction $e |- A. s e. ~P B
    (
      (
        A. x e. A
          ( NTP4VCEvar x ) e. s
        /\
        (
          A. e e. B
            (
              e e. s
              ->
              ( NTP4VCEneg e ) e. s
            )
          /\
          A. e e. B A. x e. B
            (
              (
                e e. s
                /\
                x e. s
              )
              ->
              ( NTP4VCEadd e x ) e. s
            )
        )
      )
      ->
      s = B
    ) $.

  $( Exact recursive expression evaluation. $)
  ntp4vc-eval-function $e |- C e. (
    ZZ ^m ( ( ZZ ^m A ) X. B )
  ) $.

  ntp4vc-eval-evar $e |- A. m e. ( ZZ ^m A ) A. x e. A
    (
      C ` <. m , ( NTP4VCEvar x ) >.
    )
    =
    ( m ` x ) $.

  ntp4vc-eval-eneg $e |- A. m e. ( ZZ ^m A ) A. e e. B
    (
      C ` <. m , ( NTP4VCEneg e ) >.
    )
    =
    -u ( C ` <. m , e >. ) $.

  ntp4vc-eval-eadd $e |- A. m e. ( ZZ ^m A )
    A. e e. B A. x e. B
      (
        C ` <. m , ( NTP4VCEadd e x ) >.
      )
      =
      (
        ( C ` <. m , e >. )
        +
        ( C ` <. m , x >. )
      ) $.

  $( Exact instruction execution function. $)
  ntp4vc-exec-instr-type $e |- D e. (
    ( NTP4VCState A )
    ^m
    (
      ( NTP4VCInstr A )
      X.
      ( NTP4VCState A )
    )
  ) $.

  ntp4vc-exec-load $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. x e. A
          A. r e. ZZ
            (
              D ` <.
                ( NTP4VCIload x r ) ,
                <. m , <. p , t >. >.
              >.
            )
            =
            <.
              m ,
              <.
                ( NTP4VCUpdate p r ( m ` x ) ) ,
                t
              >.
            >. $.

  ntp4vc-exec-neg $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. r e. ZZ
          (
            D ` <.
              ( NTP4VCIneg r ) ,
              <. m , <. p , t >. >.
            >.
          )
          =
          <.
            m ,
            <.
              ( NTP4VCUpdate p r ( -u ( p ` r ) ) ) ,
              t
            >.
          >. $.

  ntp4vc-exec-add $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. q e. ZZ
          A. r e. ZZ
            (
              D ` <.
                ( NTP4VCIadd q r ) ,
                <. m , <. p , t >. >.
              >.
            )
            =
            <.
              m ,
              <.
                (
                  NTP4VCUpdate
                    p r
                    ( ( p ` q ) + ( p ` r ) )
                ) ,
                t
              >.
            >. $.

  ntp4vc-exec-push $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. r e. ZZ
          (
            D ` <.
              ( NTP4VCIpush r ) ,
              <. m , <. p , t >. >.
            >.
          )
          =
          <.
            m ,
            <. p , ( <" ( p ` r ) "> ++ t ) >.
          >. $.

  ntp4vc-exec-pop-empty $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. r e. ZZ
        (
          D ` <.
            ( NTP4VCIpop r ) ,
            <. m , <. p , (/) >. >.
          >.
        )
        =
        <. m , <. p , (/) >. >. $.

  ntp4vc-exec-pop-cons $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. v e. ZZ
          A. r e. ZZ
            (
              D ` <.
                ( NTP4VCIpop r ) ,
                <. m , <. p , ( <" v "> ++ t ) >. >.
              >.
            )
            =
            <.
              m ,
              <. ( NTP4VCUpdate p r v ) , t >.
            >. $.

  $( Exact recursive execution of a finite instruction list. $)
  ntp4vc-exec-list-type $e |- E e. (
    ( NTP4VCState A )
    ^m
    (
      Word ( NTP4VCInstr A )
      X.
      ( NTP4VCState A )
    )
  ) $.

  ntp4vc-exec-list-nil $e |- A. s e. ( NTP4VCState A )
    ( E ` <. (/) , s >. ) = s $.

  ntp4vc-exec-list-cons $e |- A. i e. ( NTP4VCInstr A )
    A. l e. Word ( NTP4VCInstr A )
      A. s e. ( NTP4VCState A )
        (
          E ` <. ( <" i "> ++ l ) , s >.
        )
        =
        (
          E ` <. l , ( D ` <. i , s >. ) >.
        ) $.

  $( Source constant k, theorem parameters r and e, and their hypotheses. $)
  ntp4vc-register-count $e |- F e. ZZ $.
  ntp4vc-register-count-lower-bound $e |- 2 <_ F $.
  ntp4vc-target-register $e |- G e. ZZ $.
  ntp4vc-source-expression $e |- H e. B $.
  ntp4vc-target-register-nonnegative $e |- 0 <_ G $.
  ntp4vc-target-register-bounded $e |- G < F $.

  ntp4vc-pearl-register-allocation-finite-registers-compile-vc
    $a |- (
      ( NTP4VCBranches A B D E C F G H )
      /\
      A. o e. ( NTP4VCWCode A )
        (
          ( NTP4VCBuild A B D E C F G H o )
          ->
          (
            (
              ( NTP4VCWCodeOk A E o )
              /\
              A. x e. ( NTP4VCState A )
                <.
                  (
                    NTP4VCPostAt A
                      ( NTP4VCExprPost A C H G )
                      x
                  ) ,
                  x
                >. e. ( 1st ` o )
            )
            /\
            A. q e. ( NTP4VCHCode A )
              (
                (
                  ( NTP4VCHCodeOk A E q )
                  /\
                  ( 2nd ` q )
                  =
                  ( NTP4VCExprPost A C H G )
                )
                ->
                (
                  ( NTP4VCHCodeOk A E q )
                  /\
                  ( 2nd ` q )
                  =
                  ( NTP4VCExprPost A C H G )
                )
              )
          )
        )
    ) $.
$}
