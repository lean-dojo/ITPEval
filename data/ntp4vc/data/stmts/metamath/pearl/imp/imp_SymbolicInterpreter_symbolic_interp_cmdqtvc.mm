$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmdqtvc: the symbolic
  interpreter verification condition for skip, assignment, sequencing,
  conditional, and while commands, including symbolic-state invariants and
  bidirectional agreement with concrete execution. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  This rendering uses the same extensional encoding as the accepted
  symbolic_interp_cmd_listqtvc artifact. Program variables, expressions,
  symbolic variables, symbolic expressions, constraints, models, commands,
  configurations, symbolic states, and all semantic graphs retain their
  arbitrary source carriers. Option values and finite sets are represented
  exactly by tagged pairs and finite subsets.

  The source SymStateSet wrapper is observed in this VC only through to_fset,
  to_list followed by membership, and of_list followed by to_fset. Its mk,
  to_list, and of_list specifications therefore give a bidirectional
  extensional equivalence with finite subsets. Finset cardinal conjuncts
  attached to empty, singleton, and fresh insertion equations are omitted
  only where they are the corresponding finite-set cardinality theorem and
  hence logically equivalent to the retained equation and freshness premise.

  Constructor maps and semantic relations below are the exact source maps and
  relation graphs. NTP4VCSub expands the proposition-valued immediate-command
  match. NTP4VCBundle and NTP4VCWhileBundle expand the forward and backward
  concrete-execution specifications. The five obligation and result clauses
  are direct expansions of the two source command matches. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCOption NTP4VCSome NTP4VCFiniteSubsets NTP4VCCompose
  NTP4VCUpdate NTP4VCStateExtends NTP4VCResultsExtend NTP4VCSolution
  NTP4VCExec NTP4VCExecWhile NTP4VCOutMember NTP4VCForward
  NTP4VCBackward NTP4VCBundle NTP4VCWhileForward NTP4VCWhileBackward
  NTP4VCWhileBundle NTP4VCSub NTP4VCEvalNormal NTP4VCEvalUnbound
  NTP4VCMapped NTP4VCSymOK NTP4VCStateValid NTP4VCUpdateSpec
  NTP4VCEliminate NTP4VCBranchState NTP4VCNoSolution NTP4VCEmptyResults
  NTP4VCGuardedBundle NTP4VCConclusion NTP4VCCtxBundle
  NTP4VCCtxWhileBundle NTP4VCCtxConclusion NTP4VCCtxSymOK
  NTP4VCCtxStateValid NTP4VCCtxUpdateSpec NTP4VCCtxEliminate
  NTP4VCCtxBranchState NTP4VCCtxNoSolution NTP4VCCtxGuardedBundle
  NTP4VCCtxSub NTP4VCCtxEvalUnbound NTP4VCCtxAssignObligation
  NTP4VCCtxSeqObligation NTP4VCCtxIfObligation
  NTP4VCCtxWhileObligation NTP4VCCtxAssignResults
  NTP4VCCtxSeqResults NTP4VCCtxIfResults NTP4VCCtxWhileResults
  NTP4VCStatement 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26
  27 28 29 30 31 32 33 34 35 36
$.

$v se s2 n2 u2 l2 $.
ntp4vc-se-setvar $f setvar se $.
ntp4vc-s2-setvar $f setvar s2 $.
ntp4vc-n2-setvar $f setvar n2 $.
ntp4vc-u2-setvar $f setvar u2 $.
ntp4vc-l2-setvar $f setvar l2 $.

ntp4vc-option-syntax $a class ( NTP4VCOption A ) $.
ntp4vc-some-syntax $a class ( NTP4VCSome A ) $.
ntp4vc-finite-subsets-syntax $a class ( NTP4VCFiniteSubsets A ) $.
ntp4vc-compose-syntax $a class ( NTP4VCCompose A B C D E ) $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C D ) $.

ntp4vc-state-extends-syntax
  $a wff ( NTP4VCStateExtends A B C D ) $.
ntp4vc-results-extend-syntax
  $a wff ( NTP4VCResultsExtend A B C D E F ) $.
ntp4vc-solution-syntax
  $a wff ( NTP4VCSolution A B C D ) $.
ntp4vc-exec-syntax
  $a wff ( NTP4VCExec A B C D E F ) $.
ntp4vc-exec-while-syntax
  $a wff ( NTP4VCExecWhile A B C D E F G H ) $.
ntp4vc-out-member-syntax
  $a wff ( NTP4VCOutMember A B C D E ) $.
ntp4vc-forward-syntax
  $a wff ( NTP4VCForward A B C D E F G H I J K L M N O ) $.
ntp4vc-backward-syntax
  $a wff ( NTP4VCBackward A B C D E F G H I J K L M N O ) $.
ntp4vc-bundle-syntax
  $a wff ( NTP4VCBundle A B C D E F G H I J K L M N O P ) $.
ntp4vc-while-forward-syntax
  $a wff ( NTP4VCWhileForward A B C D E F G H I J K L M N O P ) $.
ntp4vc-while-backward-syntax
  $a wff ( NTP4VCWhileBackward A B C D E F G H I J K L M N O P ) $.
ntp4vc-while-bundle-syntax
  $a wff ( NTP4VCWhileBundle A B C D E F G H I J K L M N O P Q ) $.
ntp4vc-sub-syntax
  $a wff ( NTP4VCSub A B C D E F G ) $.
ntp4vc-eval-normal-syntax
  $a wff ( NTP4VCEvalNormal A B C D E F ) $.
ntp4vc-eval-unbound-syntax
  $a wff ( NTP4VCEvalUnbound A B C ) $.
ntp4vc-mapped-syntax
  $a wff ( NTP4VCMapped A B C D E F ) $.
ntp4vc-sym-ok-syntax
  $a wff ( NTP4VCSymOK A B C D E F G H I J K L M ) $.
ntp4vc-state-valid-syntax
  $a wff ( NTP4VCStateValid A B C D E F ) $.
ntp4vc-update-spec-syntax
  $a wff ( NTP4VCUpdateSpec A B C D E F ) $.
ntp4vc-eliminate-syntax
  $a wff ( NTP4VCEliminate A B C D E F G H I J K ) $.
ntp4vc-branch-state-syntax
  $a wff ( NTP4VCBranchState A B C D E F G H I J K L M N O ) $.
ntp4vc-no-solution-syntax
  $a wff ( NTP4VCNoSolution A B C D ) $.
ntp4vc-empty-results-syntax
  $a wff ( NTP4VCEmptyResults A B C ) $.
ntp4vc-guarded-bundle-syntax
  $a wff ( NTP4VCGuardedBundle A B C D E F G H I J K L M N O P Q ) $.
ntp4vc-conclusion-syntax
  $a wff ( NTP4VCConclusion A B C D E F G H I J K L M N O P ) $.

ntp4vc-ctx-bundle-syntax
  $a wff ( NTP4VCCtxBundle A B C D E F ) $.
ntp4vc-ctx-while-bundle-syntax
  $a wff ( NTP4VCCtxWhileBundle A B C D E F G ) $.
ntp4vc-ctx-conclusion-syntax
  $a wff ( NTP4VCCtxConclusion A B C D E F ) $.
ntp4vc-ctx-sym-ok-syntax
  $a wff ( NTP4VCCtxSymOK A B C D ) $.
ntp4vc-ctx-state-valid-syntax
  $a wff ( NTP4VCCtxStateValid A B C D ) $.
ntp4vc-ctx-update-spec-syntax
  $a wff ( NTP4VCCtxUpdateSpec A B C D E ) $.
ntp4vc-ctx-eliminate-syntax
  $a wff ( NTP4VCCtxEliminate A B C D E F ) $.
ntp4vc-ctx-branch-state-syntax
  $a wff ( NTP4VCCtxBranchState A B C D E ) $.
ntp4vc-ctx-no-solution-syntax
  $a wff ( NTP4VCCtxNoSolution A B ) $.
ntp4vc-ctx-guarded-bundle-syntax
  $a wff ( NTP4VCCtxGuardedBundle A B C D E F ) $.
ntp4vc-ctx-sub-syntax
  $a wff ( NTP4VCCtxSub A B C ) $.
ntp4vc-ctx-eval-unbound-syntax
  $a wff ( NTP4VCCtxEvalUnbound A B C ) $.
ntp4vc-ctx-assign-obligation-syntax
  $a wff ( NTP4VCCtxAssignObligation A B C D ) $.
ntp4vc-ctx-seq-obligation-syntax
  $a wff ( NTP4VCCtxSeqObligation A B C D ) $.
ntp4vc-ctx-if-obligation-syntax
  $a wff ( NTP4VCCtxIfObligation A B C D E ) $.
ntp4vc-ctx-while-obligation-syntax
  $a wff ( NTP4VCCtxWhileObligation A B C ) $.
ntp4vc-ctx-assign-results-syntax
  $a wff ( NTP4VCCtxAssignResults A B C D E F ) $.
ntp4vc-ctx-seq-results-syntax
  $a wff ( NTP4VCCtxSeqResults A B C D E F ) $.
ntp4vc-ctx-if-results-syntax
  $a wff ( NTP4VCCtxIfResults A B C D E F G ) $.
ntp4vc-ctx-while-results-syntax
  $a wff ( NTP4VCCtxWhileResults A B C D E F ) $.
ntp4vc-statement-syntax
  $a wff ( NTP4VCStatement A ) $.

ntp4vc-option-definition $a |- (
  NTP4VCOption A
) = ( ( { 0 } X. { 0 } ) u. ( { 1 } X. A ) ) $.

ntp4vc-some-definition $a |- (
  NTP4VCSome A
) = <. 1 , A >. $.

ntp4vc-finite-subsets-definition $a |- (
  NTP4VCFiniteSubsets A
) = ( ( ~P A ) i^i Fin ) $.

${
  $d x A B C D E $.
  ntp4vc-compose-definition $a |- (
    NTP4VCCompose A B C D E
  ) = (
    x e. A |->
      if (
        ( 1st ` ( D ` <. ( C ` E ) , x >. ) ) = 0 ,
        <. 0 , 0 >. ,
        (
          NTP4VCSome
          ( ( B ` E ) ` ( 2nd ` ( D ` <. ( C ` E ) , x >. ) ) )
        )
      )
  ) $.
$}

$(
  The single context parameter used below is a definitional package.  Its
  components 0 through 36 are, in order: program-variable, expression,
  symbolic-variable, symbolic-expression, constraint, model, command,
  loop-configuration, and symbolic-state carriers; skip, assignment,
  sequence, conditional, and while constructors; rho, sigma, constraint, and
  variable-set projections; get, set, interpretation, symbolic-expression
  variables, and constraint variables; Slit, Svar, Ceq, Cneq, Cconj, and
  Cexists; solution, expression-evaluation, command-execution, while-execution,
  and loop-configuration graphs; and finally n, c, and s.
$)

ntp4vc-ctx-bundle-definition $a |- (
  NTP4VCCtxBundle A B C D E F
) <-> (
  NTP4VCBundle
    B C D E ( A ` 34 ) F ( A ` 0 ) ( A ` 14 ) ( A ` 15 )
    ( A ` 18 ) ( A ` 29 ) ( A ` 16 ) ( A ` 31 ) ( A ` 33 )
    ( A ` 8 ) ( A ` 17 )
) $.

ntp4vc-ctx-while-bundle-definition $a |- (
  NTP4VCCtxWhileBundle A B C D E F G
) <-> (
  NTP4VCWhileBundle
    B C D E ( A ` 34 ) F ( A ` 0 ) ( A ` 14 ) ( A ` 15 )
    ( A ` 18 ) ( A ` 29 ) ( A ` 16 ) ( A ` 32 ) ( A ` 33 )
    G ( A ` 8 ) ( A ` 17 )
) $.

ntp4vc-ctx-conclusion-definition $a |- (
  NTP4VCCtxConclusion A B C D E F
) <-> (
  NTP4VCConclusion
    B C D E ( A ` 34 ) F ( A ` 0 ) ( A ` 14 ) ( A ` 15 )
    ( A ` 18 ) ( A ` 29 ) ( A ` 16 ) ( A ` 31 ) ( A ` 33 )
    ( A ` 8 ) ( A ` 17 )
) $.

ntp4vc-ctx-sym-ok-definition $a |- (
  NTP4VCCtxSymOK A B C D
) <-> (
  (
    NTP4VCEvalNormal
      ( A ` 30 )
      ( NTP4VCCompose ( A ` 0 ) ( A ` 14 ) ( A ` 15 ) ( A ` 18 ) B )
      C ( ( A ` 14 ) ` B ) ( A ` 20 ) D
  )
  /\
  ( NTP4VCMapped ( A ` 0 ) B ( A ` 15 ) ( A ` 18 ) ( A ` 21 ) D )
) $.

${
  $d v x A B C D $.
  ntp4vc-ctx-state-valid-definition $a |- (
    NTP4VCCtxStateValid A B C D
  ) <-> (
    ( ( A ` 22 ) ` C ) C_ D
    /\
    A. x e. ( A ` 0 ) A. v e. ( A ` 2 )
      (
        ( ( A ` 18 ) ` <. B , x >. ) = ( NTP4VCSome v )
        ->
        v e. D
      )
  ) $.
$}

${
  $d k A B C D E $.
  ntp4vc-ctx-update-spec-definition $a |- (
    NTP4VCCtxUpdateSpec A B C D E
  ) <-> (
    (
      E = ( ( A ` 19 ) ` <. ( ( A ` 15 ) ` B ) , <. C , D >. >. )
      /\
      ( ( A ` 18 ) ` <. E , C >. ) = ( NTP4VCSome D )
    )
    /\
    A. k e. ( A ` 0 )
      (
        -. k = C
        ->
        ( ( A ` 18 ) ` <. E , k >. )
          =
        ( ( A ` 18 ) ` <. ( ( A ` 15 ) ` B ) , k >. )
      )
  ) $.
$}

${
  $d r v A B C D E F $.
  ntp4vc-ctx-eliminate-definition $a |- (
    NTP4VCCtxEliminate A B C D E F
  ) <-> (
    (
      E. v e. ( A ` 2 )
        (
          ( ( A ` 18 ) ` <. ( ( A ` 15 ) ` C ) , D >. )
            =
          ( NTP4VCSome v )
          /\
          (
            A. r e. ( ZZ ^m ( A ` 2 ) )
              (
                <. r , B >. e. ( A ` 29 )
                <->
                <.
                  r ,
                  (
                    ( A ` 28 )
                    `
                    <.
                      v ,
                      (
                        ( A ` 27 )
                        `
                        <.
                          ( ( A ` 16 ) ` C ) ,
                          (
                            ( A ` 25 )
                            `
                            <. ( ( A ` 24 ) ` E ) , F >.
                          )
                        >.
                      )
                    >.
                  )
                >. e. ( A ` 29 )
              )
          )
          /\
          ( ( A ` 22 ) ` B )
            C_
          (
            ( A ` 22 )
            `
            (
              ( A ` 28 )
              `
              <.
                v ,
                (
                  ( A ` 27 )
                  `
                  <.
                    ( ( A ` 16 ) ` C ) ,
                    ( ( A ` 25 ) ` <. ( ( A ` 24 ) ` E ) , F >. )
                  >.
                )
              >.
            )
          )
        )
    )
    \/
    (
      ( ( A ` 18 ) ` <. ( ( A ` 15 ) ` C ) , D >. ) = <. 0 , 0 >.
      /\
      B
      =
      (
        ( A ` 27 )
        `
        <.
          ( ( A ` 16 ) ` C ) ,
          ( ( A ` 25 ) ` <. ( ( A ` 24 ) ` E ) , F >. )
        >.
      )
    )
  ) $.
$}

ntp4vc-ctx-branch-state-definition $a |- (
  NTP4VCCtxBranchState A B C D E
) <-> (
  (
    ( ( A ` 15 ) ` B ) = ( ( A ` 15 ) ` C )
    /\
    (
      ( ( A ` 16 ) ` B )
      =
      if (
        D = 1 ,
        (
          ( A ` 27 )
          `
          <.
            ( ( A ` 16 ) ` C ) ,
            ( ( A ` 26 ) ` <. E , ( ( A ` 23 ) ` 0 ) >. )
          >.
        ) ,
        (
          ( A ` 27 )
          `
          <.
            ( ( A ` 16 ) ` C ) ,
            ( ( A ` 25 ) ` <. E , ( ( A ` 23 ) ` 0 ) >. )
          >.
        )
      )
    )
  )
  /\
  (
    ( ( A ` 14 ) ` B ) = ( ( A ` 14 ) ` C )
    /\
    ( ( A ` 17 ) ` B ) = ( ( A ` 17 ) ` C )
  )
) $.

${
  $d r A B $.
  ntp4vc-ctx-no-solution-definition $a |- (
    NTP4VCCtxNoSolution A B
  ) <-> (
    A. r e. ( ZZ ^m ( A ` 2 ) )
      -. <. r , ( ( A ` 16 ) ` B ) >. e. ( A ` 29 )
  ) $.
$}

ntp4vc-ctx-guarded-bundle-definition $a |- (
  NTP4VCCtxGuardedBundle A B C D E F
) <-> (
  E. t e. { 0 , 1 }
    (
      ( t = 0 -> ( NTP4VCCtxNoSolution A B ) )
      /\
      if (
        t = 1 ,
        ( NTP4VCCtxBundle A B C D E F ) ,
        ( NTP4VCEmptyResults C D E )
      )
    )
) $.

ntp4vc-ctx-sub-definition $a |- (
  NTP4VCCtxSub A B C
) <-> (
  NTP4VCSub B C ( A ` 6 ) ( A ` 1 ) ( A ` 13 ) ( A ` 11 ) ( A ` 12 )
) $.

ntp4vc-ctx-eval-unbound-definition $a |- (
  NTP4VCCtxEvalUnbound A B C
) <-> (
  NTP4VCEvalUnbound
    ( A ` 30 )
    ( NTP4VCCompose ( A ` 0 ) ( A ` 14 ) ( A ` 15 ) ( A ` 18 ) B )
    C
) $.

${
  $d se v w A B C D $.
  ntp4vc-ctx-assign-obligation-definition $a |- (
    NTP4VCCtxAssignObligation A B C D
  ) <-> (
    A. se e. ( A ` 3 )
      (
        ( NTP4VCCtxSymOK A B D se )
        ->
        A. v e. ( A ` 2 )
          (
            -. v e. ( ( A ` 17 ) ` B )
            ->
            A. w e. ( A ` 5 )
              (
                ( NTP4VCCtxUpdateSpec A B C v w )
                ->
                A. k e. ( A ` 4 )
                  (
                    ( NTP4VCCtxEliminate A k B C v se )
                    ->
                    A. u e. ( NTP4VCFiniteSubsets ( A ` 2 ) )
                      (
                        u = ( { v } u. ( ( A ` 17 ) ` B ) )
                        ->
                        ( NTP4VCCtxStateValid A w k u )
                      )
                  )
              )
          )
      )
  ) $.
$}

${
  $d l1 n1 u1 A B C D $.
  ntp4vc-ctx-seq-obligation-definition $a |- (
    NTP4VCCtxSeqObligation A B C D
  ) <-> (
    (
      ( NTP4VCCtxSub A ( A ` 35 ) C )
      /\
      0 <_ ( A ` 34 )
    )
    /\
    A. n1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
    A. u1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
    A. l1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
      (
        ( NTP4VCCtxBundle A B n1 u1 l1 C )
        ->
        (
          ( NTP4VCCtxSub A ( A ` 35 ) D )
          /\
          0 <_ ( A ` 34 )
        )
      )
  ) $.
$}

${
  $d l1 n1 s1 s2 se u1 A B C D E $.
  ntp4vc-ctx-if-obligation-definition $a |- (
    NTP4VCCtxIfObligation A B C D E
  ) <-> (
    A. se e. ( A ` 3 )
      (
        ( NTP4VCCtxSymOK A B C se )
        ->
        (
          (
            NTP4VCCtxStateValid
              A
              ( ( A ` 15 ) ` B )
              (
                ( A ` 27 )
                `
                <.
                  ( ( A ` 16 ) ` B ) ,
                  ( ( A ` 26 ) ` <. se , ( ( A ` 23 ) ` 0 ) >. )
                >.
              )
              ( ( A ` 17 ) ` B )
          )
          /\
          A. s1 e. ( A ` 8 )
            (
              ( NTP4VCCtxBranchState A s1 B 1 se )
              ->
              (
                (
                  NTP4VCCtxStateValid
                    A
                    ( ( A ` 15 ) ` B )
                    (
                      ( A ` 27 )
                      `
                      <.
                        ( ( A ` 16 ) ` B ) ,
                        ( ( A ` 25 ) ` <. se , ( ( A ` 23 ) ` 0 ) >. )
                      >.
                    )
                    ( ( A ` 17 ) ` B )
                )
                /\
                A. s2 e. ( A ` 8 )
                  (
                    ( NTP4VCCtxBranchState A s2 B 0 se )
                    ->
                    (
                      (
                        ( NTP4VCCtxSub A ( A ` 35 ) D )
                        /\
                        0 <_ ( A ` 34 )
                      )
                      /\
                      A. n1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
                      A. u1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
                      A. l1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
                        (
                          ( NTP4VCCtxGuardedBundle A s1 n1 u1 l1 D )
                          ->
                          (
                            ( NTP4VCCtxSub A ( A ` 35 ) E )
                            /\
                            0 <_ ( A ` 34 )
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

ntp4vc-ctx-while-obligation-definition $a |- (
  NTP4VCCtxWhileObligation A B C
) <-> (
  (
    (
      ( NTP4VCCtxSub A ( A ` 35 ) ( ( A ` 13 ) ` <. B , C >. ) )
      \/
      (
        ( A ` 35 ) = ( ( A ` 13 ) ` <. B , C >. )
        /\
        (
          0 <_ ( ( A ` 34 ) + 1 )
          /\
          ( ( A ` 34 ) - 0 ) < ( ( A ` 34 ) + 1 )
        )
      )
    )
    /\
    0 <_ 0
  )
  /\
  0 <_ ( A ` 34 )
) $.

${
  $d se s1 v w A B C D E F $.
  ntp4vc-ctx-assign-results-definition $a |- (
    NTP4VCCtxAssignResults A B C D E F
  ) <-> (
    (
      E. se e. ( A ` 3 )
        (
          ( NTP4VCCtxSymOK A ( A ` 36 ) C se )
          /\
          E. v e. ( A ` 2 )
            (
              -. v e. ( ( A ` 17 ) ` ( A ` 36 ) )
              /\
              E. w e. ( A ` 5 )
                (
                  ( NTP4VCCtxUpdateSpec A ( A ` 36 ) B v w )
                  /\
                  E. k e. ( A ` 4 )
                    (
                      ( NTP4VCCtxEliminate A k ( A ` 36 ) B v se )
                      /\
                      E. u e. ( NTP4VCFiniteSubsets ( A ` 2 ) )
                        (
                          u = ( { v } u. ( ( A ` 17 ) ` ( A ` 36 ) ) )
                          /\
                          E. s1 e. ( A ` 8 )
                            (
                              (
                                ( ( A ` 15 ) ` s1 ) = w
                                /\
                                ( ( A ` 16 ) ` s1 ) = k
                              )
                              /\
                              (
                                (
                                  ( ( A ` 14 ) ` s1 )
                                  =
                                  (
                                    NTP4VCUpdate
                                      ( A ` 2 )
                                      ( ( A ` 14 ) ` ( A ` 36 ) )
                                      v
                                      (
                                        ( ( A ` 20 ) ` ( ( A ` 14 ) ` ( A ` 36 ) ) )
                                        `
                                        se
                                      )
                                  )
                                )
                                /\
                                ( ( A ` 17 ) ` s1 ) = u
                              )
                              /\
                              (
                                ( F = (/) /\ E = (/) )
                                /\
                                D = { s1 }
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
      ( NTP4VCCtxEvalUnbound A ( A ` 36 ) C )
      /\
      (
        ( F = (/) /\ E = { ( A ` 36 ) } )
        /\
        D = (/)
      )
    )
  ) $.
$}

${
  $d l1 l2 n1 u1 u2 A B C D E F $.
  ntp4vc-ctx-seq-results-definition $a |- (
    NTP4VCCtxSeqResults A B C D E F
  ) <-> (
    E. n1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
    E. u1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
    E. l1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
      (
        ( NTP4VCCtxBundle A ( A ` 36 ) n1 u1 l1 B )
        /\
        E. u2 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
        E. l2 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
          (
            ( NTP4VCCtxConclusion A n1 D u2 l2 C )
            /\
            (
              ( F = ( l1 u. l2 ) /\ E = ( u1 u. u2 ) )
              /\
              D = D
            )
          )
      )
  ) $.
$}

${
  $d l1 l2 n1 n2 s1 s2 se u1 u2 A B C D E F G $.
  ntp4vc-ctx-if-results-definition $a |- (
    NTP4VCCtxIfResults A B C D E F G
  ) <-> (
    (
      E. se e. ( A ` 3 )
        (
          ( NTP4VCCtxSymOK A ( A ` 36 ) B se )
          /\
          E. s1 e. ( A ` 8 ) E. s2 e. ( A ` 8 )
            (
              (
                ( NTP4VCCtxBranchState A s1 ( A ` 36 ) 1 se )
                /\
                ( NTP4VCCtxBranchState A s2 ( A ` 36 ) 0 se )
              )
              /\
              E. n1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
              E. u1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
              E. l1 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
              E. n2 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
              E. u2 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
              E. l2 e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
                (
                  (
                    ( NTP4VCCtxGuardedBundle A s1 n1 u1 l1 C )
                    /\
                    ( NTP4VCCtxGuardedBundle A s2 n2 u2 l2 D )
                  )
                  /\
                  (
                    ( G = ( l1 u. l2 ) /\ F = ( u1 u. u2 ) )
                    /\
                    E = ( n1 u. n2 )
                  )
                )
            )
        )
    )
    \/
    (
      ( NTP4VCCtxEvalUnbound A ( A ` 36 ) B )
      /\
      (
        ( G = (/) /\ F = { ( A ` 36 ) } )
        /\
        E = (/)
      )
    )
  ) $.
$}

ntp4vc-ctx-while-results-definition $a |- (
  NTP4VCCtxWhileResults A B C D E F
) <-> (
  (
    NTP4VCCtxWhileBundle
      A ( A ` 36 ) D E F B C
  )
  ->
  (
    NTP4VCCtxBundle
      A ( A ` 36 ) D E F ( A ` 35 )
  )
) $.

${
  $d e l n p q u x A $.
  ntp4vc-statement-definition $a |- (
    NTP4VCStatement A
  ) <-> (
    (
      (
        A. x e. ( A ` 0 ) A. e e. ( A ` 1 )
          (
            ( A ` 35 ) = ( ( A ` 10 ) ` <. x , e >. )
            ->
            ( NTP4VCCtxAssignObligation A ( A ` 36 ) x e )
          )
      )
      /\
      (
        A. p e. ( A ` 6 ) A. q e. ( A ` 6 )
          (
            ( A ` 35 ) = ( ( A ` 11 ) ` <. p , q >. )
            ->
            ( NTP4VCCtxSeqObligation A ( A ` 36 ) p q )
          )
      )
      /\
      (
        A. e e. ( A ` 1 ) A. p e. ( A ` 6 ) A. q e. ( A ` 6 )
          (
            ( A ` 35 ) = ( ( A ` 12 ) ` <. e , <. p , q >. >. )
            ->
            ( NTP4VCCtxIfObligation A ( A ` 36 ) e p q )
          )
      )
      /\
      A. e e. ( A ` 1 ) A. p e. ( A ` 6 )
        (
          ( A ` 35 ) = ( ( A ` 13 ) ` <. e , p >. )
          ->
          ( NTP4VCCtxWhileObligation A e p )
        )
    )
    /\
    A. n e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
    A. u e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
    A. l e. ( NTP4VCFiniteSubsets ( A ` 8 ) )
      (
        (
          (
            ( A ` 35 ) = ( A ` 9 )
            ->
            (
              ( l = (/) /\ u = (/) )
              /\
              n = { ( A ` 36 ) }
            )
          )
          /\
          A. x e. ( A ` 0 ) A. e e. ( A ` 1 )
            (
              ( A ` 35 ) = ( ( A ` 10 ) ` <. x , e >. )
              ->
              ( NTP4VCCtxAssignResults A x e n u l )
            )
        )
        /\
        (
          A. p e. ( A ` 6 ) A. q e. ( A ` 6 )
            (
              ( A ` 35 ) = ( ( A ` 11 ) ` <. p , q >. )
              ->
              ( NTP4VCCtxSeqResults A p q n u l )
            )
        )
        /\
        (
          A. e e. ( A ` 1 ) A. p e. ( A ` 6 ) A. q e. ( A ` 6 )
            (
              ( A ` 35 ) = ( ( A ` 12 ) ` <. e , <. p , q >. >. )
              ->
              ( NTP4VCCtxIfResults A e p q n u l )
            )
        )
        /\
        A. e e. ( A ` 1 ) A. p e. ( A ` 6 )
          (
            ( A ` 35 ) = ( ( A ` 13 ) ` <. e , p >. )
            ->
            ( NTP4VCCtxWhileResults A e p n u l )
          )
      )
  ) $.
$}

${
  $d x A B C D $.
  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C D
  ) = (
    x e. A |-> if ( x = C , D , ( B ` x ) )
  ) $.
$}

${
  $d v A B C D $.
  ntp4vc-state-extends-definition $a |- (
    NTP4VCStateExtends A B C D
  ) <-> (
    ( C ` A ) C_ ( C ` B )
    /\
    A. v e. ( C ` A ) ( ( D ` A ) ` v ) = ( ( D ` B ) ` v )
  ) $.
$}

${
  $d t A B C D E F $.
  ntp4vc-results-extend-definition $a |- (
    NTP4VCResultsExtend A B C D E F
  ) <-> (
    A. t e. ( ( B u. C ) u. D )
      ( NTP4VCStateExtends A t E F )
  ) $.
$}

ntp4vc-solution-definition $a |- (
  NTP4VCSolution A B C D
) <-> ( <. ( B ` D ) , ( C ` D ) >. e. A ) $.

ntp4vc-exec-definition $a |- (
  NTP4VCExec A B C D E F
) <-> (
  <. <. <. <. B , C >. , D >. , E >. , F >. e. A
) $.

ntp4vc-exec-while-definition $a |- (
  NTP4VCExecWhile A B C D E F G H
) <-> (
  <. <. <. <. <. <. B , C >. , D >. , E >. , F >. , G >. , H >. e. A
) $.

ntp4vc-out-member-definition $a |- (
  NTP4VCOutMember A B C D E
) <-> (
  ( ( A = 0 /\ B e. C ) \/ ( A = 1 /\ B e. D ) )
  \/
  ( A = 2 /\ B e. E )
) $.

${
  $d b g t A B C D E F G H I J K L M N O $.
  ntp4vc-forward-definition $a |- (
    NTP4VCForward A B C D E F G H I J K L M N O
  ) <-> (
    A. g e. ( ( NTP4VCOption ZZ ) ^m G ) A. b e. { 0 , 1 , 2 }
      (
        ( NTP4VCExec M ( N ` E ) ( NTP4VCCompose G H I J A ) F g b )
        ->
        E. t e. O
          (
            ( NTP4VCOutMember b t B C D )
            /\
            (
              ( NTP4VCSolution K H L t )
              /\
              g = ( NTP4VCCompose G H I J t )
            )
          )
      )
  ) $.
$}

${
  $d b t A B C D E F G H I J K L M N O $.
  ntp4vc-backward-definition $a |- (
    NTP4VCBackward A B C D E F G H I J K L M N O
  ) <-> (
    A. b e. { 0 , 1 , 2 } A. t e. O
      (
        ( NTP4VCOutMember b t B C D )
        ->
        (
          ( NTP4VCSolution K H L t )
          ->
          (
            ( NTP4VCSolution K H L A )
            /\
            (
              NTP4VCExec M ( N ` E ) ( NTP4VCCompose G H I J A )
                F ( NTP4VCCompose G H I J t ) b
            )
          )
        )
      )
  ) $.
$}

ntp4vc-bundle-definition $a |- (
  NTP4VCBundle A B C D E F G H I J K L M N O P
) <-> (
  ( NTP4VCResultsExtend A B C D P H )
  /\
  (
    (
      ( NTP4VCSolution K H L A )
      ->
      ( NTP4VCForward A B C D E F G H I J K L M N O )
    )
    /\
    ( NTP4VCBackward A B C D E F G H I J K L M N O )
  )
) $.

${
  $d b g t A B C D E F G H I J K L M N O P $.
  ntp4vc-while-forward-definition $a |- (
    NTP4VCWhileForward A B C D E F G H I J K L M N O P
  ) <-> (
    A. g e. ( ( NTP4VCOption ZZ ) ^m G ) A. b e. { 0 , 1 , 2 }
      (
        (
          NTP4VCExecWhile M ( N ` E ) 0
            ( NTP4VCCompose G H I J A ) F O g b
        )
        ->
        E. t e. P
          (
            ( NTP4VCOutMember b t B C D )
            /\
            (
              ( NTP4VCSolution K H L t )
              /\
              g = ( NTP4VCCompose G H I J t )
            )
          )
      )
  ) $.
$}

${
  $d b t A B C D E F G H I J K L M N O P $.
  ntp4vc-while-backward-definition $a |- (
    NTP4VCWhileBackward A B C D E F G H I J K L M N O P
  ) <-> (
    A. b e. { 0 , 1 , 2 } A. t e. P
      (
        ( NTP4VCOutMember b t B C D )
        ->
        (
          ( NTP4VCSolution K H L t )
          ->
          (
            ( NTP4VCSolution K H L A )
            /\
            (
              NTP4VCExecWhile M ( N ` E ) 0
                ( NTP4VCCompose G H I J A ) F O
                ( NTP4VCCompose G H I J t ) b
            )
          )
        )
      )
  ) $.
$}

ntp4vc-while-bundle-definition $a |- (
  NTP4VCWhileBundle A B C D E F G H I J K L M N O P Q
) <-> (
  ( NTP4VCResultsExtend A B C D Q H )
  /\
  (
    (
      ( NTP4VCSolution K H L A )
      ->
      ( NTP4VCWhileForward A B C D E F G H I J K L M N O P )
    )
    /\
    ( NTP4VCWhileBackward A B C D E F G H I J K L M N O P )
  )
) $.

${
  $d e p q x A B C D E F G $.
  ntp4vc-sub-definition $a |- (
    NTP4VCSub A B C D E F G
  ) <-> (
    (
      E. p e. C E. q e. C
        ( A = ( F ` <. p , q >. ) /\ ( B = p \/ B = q ) )
    )
    \/
    (
      (
        E. e e. D E. p e. C E. q e. C
          ( A = ( G ` <. e , <. p , q >. >. ) /\ ( B = p \/ B = q ) )
      )
      \/
      E. e e. D E. p e. C
        ( A = ( E ` <. e , p >. ) /\ B = p )
    )
  ) $.
$}

ntp4vc-eval-normal-definition $a |- (
  NTP4VCEvalNormal A B C D E F
) <-> (
  <. <. B , C >. , <. 0 , ( ( E ` D ) ` F ) >. >. e. A
) $.

ntp4vc-eval-unbound-definition $a |- (
  NTP4VCEvalUnbound A B C
) <-> (
  <. <. B , C >. , <. 1 , 0 >. >. e. A
) $.

${
  $d v x A B C D E F $.
  ntp4vc-mapped-definition $a |- (
    NTP4VCMapped A B C D E F
  ) <-> (
    A. v e. ( E ` F )
      E. x e. A ( D ` <. ( C ` B ) , x >. ) = ( NTP4VCSome v )
  ) $.
$}

ntp4vc-sym-ok-definition $a |- (
  NTP4VCSymOK A B C D E F G H I J K L M
) <-> (
  (
    NTP4VCEvalNormal
      A ( NTP4VCCompose C D E F B ) G ( D ` B ) H I
  )
  /\
  ( NTP4VCMapped J B C E F K I )
) $.

${
  $d v x A B C D E F $.
  ntp4vc-state-valid-definition $a |- (
    NTP4VCStateValid A B C D E F
  ) <-> (
    ( E ` B ) C_ C
    /\
    A. x e. A A. v e. D
      (
        ( F ` <. B , x >. ) = ( NTP4VCSome v )
        ->
        v e. C
      )
  ) $.
$}

${
  $d k A B C D E F $.
  ntp4vc-update-spec-definition $a |- (
    NTP4VCUpdateSpec A B C D E F
  ) <-> (
    (
      ( E ` <. D , B >. ) = ( NTP4VCSome C )
      /\
      A. k e. A
        ( -. k = B -> ( E ` <. D , k >. ) = ( E ` <. F , k >. ) )
    )
  ) $.
$}

${
  $d r v A B C D E F G H I J K $.
  ntp4vc-eliminate-definition $a |- (
    NTP4VCEliminate A B C D E F G H I J K
  ) <-> (
    (
      E. v e. G
        (
          ( E ` <. ( D ` B ) , C >. ) = ( NTP4VCSome v )
          /\
          (
            (
              A. r e. ( ZZ ^m G )
                (
                  ( NTP4VCSolution F r D A )
                  <->
                  ( NTP4VCSolution F r D ( J ` <. v , H >. ) )
                )
            )
            /\
            ( I ` A ) C_ ( I ` ( J ` <. v , H >. ) )
          )
        )
    )
    \/
    (
      ( E ` <. ( D ` B ) , C >. ) = <. 0 , 0 >.
      /\
      A = H
    )
  ) $.
$}

ntp4vc-branch-state-definition $a |- (
  NTP4VCBranchState A B C D E F G H I J K L M N O
) <-> (
  (
    ( H ` A ) = ( H ` B )
    /\
    (
      ( I ` A )
      =
      if (
        C = 1 ,
        ( M ` <. ( I ` B ) , ( N ` <. D , ( O ` 0 ) >. ) >. ) ,
        ( M ` <. ( I ` B ) , ( L ` <. D , ( O ` 0 ) >. ) >. )
      )
    )
  )
  /\
  ( ( J ` A ) = ( J ` B ) /\ ( K ` A ) = ( K ` B ) )
) $.

${
  $d r A B C D $.
  ntp4vc-no-solution-definition $a |- (
    NTP4VCNoSolution A B C D
  ) <-> (
    A. r e. ( ZZ ^m C ) -. ( NTP4VCSolution A r B D )
  ) $.
$}

ntp4vc-empty-results-definition $a |- (
  NTP4VCEmptyResults A B C
) <-> ( ( A = (/) /\ B = (/) ) /\ C = (/) ) $.

ntp4vc-guarded-bundle-definition $a |- (
  NTP4VCGuardedBundle A B C D E F G H I J K L M N O P Q
) <-> (
  E. t e. { 0 , 1 }
    (
      ( t = 0 -> ( NTP4VCNoSolution K H L A ) )
      /\
      if (
        t = 1 ,
        ( NTP4VCBundle A B C D E F G H I J K L M N O P Q ) ,
        ( NTP4VCEmptyResults B C D )
      )
    )
) $.

${
  $d b g s t A B C D E F G H I J K L M N O P $.
  ntp4vc-conclusion-definition $a |- (
    NTP4VCConclusion A B C D E F G H I J K L M N O P
  ) <-> (
    (
      A. t e. ( ( B u. C ) u. D )
        E. s e. A ( NTP4VCStateExtends s t P H )
    )
    /\
    (
      (
        A. s e. A
          (
            ( NTP4VCSolution K H L s )
            ->
            ( NTP4VCForward s B C D E F G H I J K L M N O )
          )
      )
      /\
      A. b e. { 0 , 1 , 2 } A. t e. O
        (
          ( NTP4VCOutMember b t B C D )
          ->
          (
            ( NTP4VCSolution K H L t )
            ->
            E. s e. A
              (
                ( NTP4VCSolution K H L s )
                /\
                (
                  NTP4VCExec M ( N ` E ) ( NTP4VCCompose G H I J s )
                    F ( NTP4VCCompose G H I J t ) b
                )
              )
          )
        )
    )
  ) $.
$}

$(
  The following block is the retired pre-review high-arity encoding.  It is
  retained only as historical text and is not part of the Metamath database.

${
  $d k r se v w x A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-assign-obligation-definition $a |- (
    NTP4VCAssignObligation
      A B C D E F G H I J K L M N O P Q R S T U V W
  ) <-> (
    A. se e. F
      (
        ( NTP4VCSymOK G A H I J B U V K L M W se )
        ->
        A. v e. E
          (
            -. v e. ( J ` A )
            ->
            (
              NTP4VCUpdateSpec
                H C v ( T ` <. ( I ` A ) , <. C , v >. >. ) K ( I ` A )
              ->
              A. w e. D
                (
                  NTP4VCEliminate
                    w A C I K P E Q R
                    ( N ` <. ( J ` A ) , ( O ` <. ( M ` v ) , se >. ) >. )
                    S
                  ->
                  A. r e. ( NTP4VCFiniteSubsets E )
                    (
                      r = ( { v } u. ( J ` A ) )
                      ->
                      (
                        NTP4VCStateValid
                          H ( T ` <. ( I ` A ) , <. C , v >. >. )
                          r E R K
                      )
                    )
                )
            )
          )
      )
  ) $.
$}

${
  $d l n u A B C D E F G H I J K L M N O P Q R S T $.
  ntp4vc-seq-obligation-definition $a |- (
    NTP4VCSeqObligation A B C D E F G H I J K L M N O P Q R S T
  ) <-> (
    (
      ( NTP4VCSub A B J K L M N /\ 0 <_ D )
      /\
      A. n e. ( NTP4VCFiniteSubsets I )
        A. u e. ( NTP4VCFiniteSubsets I )
          A. l e. ( NTP4VCFiniteSubsets I )
            (
              ( NTP4VCBundle E n u l D B F G H O P Q R S T I J )
              ->
              ( NTP4VCSub A C J K L M N /\ 0 <_ D )
            )
    )
  ) $.
$}

${
  $d l n se s1 s2 u A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-if-obligation-definition $a |- (
    NTP4VCIfObligation
      A B C D E F G H I J K L M N O P Q R S T U V W
  ) <-> (
    A. se e. F
      (
        ( NTP4VCSymOK G A H I J B U V K L M W se )
        ->
        E. s1 e. E E. s2 e. E
          (
            (
              NTP4VCBranchState s1 A 1 se H I J K L M N O P Q R
              /\
              NTP4VCBranchState s2 A 0 se H I J K L M N O P Q R
            )
            /\
            (
              ( NTP4VCSub C D H I S T V /\ 0 <_ B )
              /\
              A. n e. ( NTP4VCFiniteSubsets E )
                A. u e. ( NTP4VCFiniteSubsets E )
                  A. l e. ( NTP4VCFiniteSubsets E )
                    (
                      (
                        NTP4VCGuardedBundle
                          s1 n u l B D H I J K L M N O P Q E
                      )
                      ->
                      ( NTP4VCSub C F H I S T V /\ 0 <_ B )
                    )
            )
          )
      )
  ) $.
$}

ntp4vc-while-obligation-definition $a |- (
  NTP4VCWhileObligation A B C D E F G H I
) <-> (
  (
    (
      ( NTP4VCSub A A D E F G H )
      \/
      (
        A = ( H ` <. B , C >. )
        /\
        ( 0 <_ ( I + 1 ) /\ ( I - 0 ) < ( I + 1 ) )
      )
    )
    /\
    ( 0 <_ 0 /\ 0 <_ I )
  )
) $.

${
  $d r se s1 v w A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-assign-results-definition $a |- (
    NTP4VCAssignResults
      A B C D E F G H I J K L M N O P Q R S T U V W
  ) <-> (
    (
      E. se e. F
        (
          ( NTP4VCSymOK G A H I J B U V K L M W se )
          /\
          E. v e. E
            (
              -. v e. ( J ` A )
              /\
              (
                NTP4VCUpdateSpec
                  H C v ( T ` <. ( I ` A ) , <. C , v >. >. ) K ( I ` A )
                /\
                E. w e. D
                  (
                    NTP4VCEliminate
                      w A C I K P E Q R
                      ( N ` <. ( J ` A ) , ( O ` <. ( M ` v ) , se >. ) >. )
                      S
                    /\
                    E. r e. ( NTP4VCFiniteSubsets E )
                      (
                        r = ( { v } u. ( J ` A ) )
                        /\
                        E. s1 e. L
                          (
                            (
                              (
                                ( I ` s1 )
                                =
                                ( T ` <. ( I ` A ) , <. C , v >. >. )
                              )
                              /\
                              ( K ` s1 ) = w
                            )
                            /\
                            (
                              (
                                ( P ` s1 )
                                =
                                ( NTP4VCUpdate E ( P ` A ) v ( ( U ` ( P ` A ) ) ` se ) )
                              )
                              /\
                              ( J ` s1 ) = r
                            )
                            /\
                            (
                              ( NTP4VCEmptyResults B D )
                              /\
                              C = { s1 }
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
      ( NTP4VCEvalUnbound G ( NTP4VCCompose H P I K A ) B )
      /\
      ( ( D = (/) /\ C = { A } ) /\ B = B )
    )
  ) $.
$}

${
  $d l l1 l2 n n1 u u1 u2 A B C D E F G H I J K L M N O P Q R S T $.
  ntp4vc-seq-results-definition $a |- (
    NTP4VCSeqResults A B C D E F G H I J K L M N O P Q R S T
  ) <-> (
    E. n1 e. ( NTP4VCFiniteSubsets I )
      E. u1 e. ( NTP4VCFiniteSubsets I )
        E. l1 e. ( NTP4VCFiniteSubsets I )
          (
            ( NTP4VCBundle E n1 u1 l1 D B F G H O P Q R S T I J )
            /\
            E. u2 e. ( NTP4VCFiniteSubsets I )
              E. l2 e. ( NTP4VCFiniteSubsets I )
                (
                  (
                    NTP4VCConclusion
                      n1 A u2 l2 D C F G H O P Q R S T
                  )
                  /\
                  ( L = ( l1 u. l2 ) /\ K = ( u1 u. u2 ) )
                )
          )
  ) $.
$}

${
  $d l1 l2 n1 n2 se s1 s2 u1 u2
     A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-if-results-definition $a |- (
    NTP4VCIfResults
      A B C D E F G H I J K L M N O P Q R S T U V W
  ) <-> (
    (
      E. se e. F
        (
          ( NTP4VCSymOK G A H I J B U V K L M W se )
          /\
          E. s1 e. E E. s2 e. E
            (
              (
                NTP4VCBranchState s1 A 1 se H I J K L M N O P Q R
                /\
                NTP4VCBranchState s2 A 0 se H I J K L M N O P Q R
              )
              /\
              E. n1 e. ( NTP4VCFiniteSubsets E )
                E. u1 e. ( NTP4VCFiniteSubsets E )
                  E. l1 e. ( NTP4VCFiniteSubsets E )
                    (
                      (
                        NTP4VCGuardedBundle
                          s1 n1 u1 l1 B C H I J K L M N O P Q E
                      )
                      /\
                      E. n2 e. ( NTP4VCFiniteSubsets E )
                        E. u2 e. ( NTP4VCFiniteSubsets E )
                          E. l2 e. ( NTP4VCFiniteSubsets E )
                            (
                              (
                                NTP4VCGuardedBundle
                                  s2 n2 u2 l2 B D H I J K L M N O P Q E
                              )
                              /\
                              (
                                ( V = ( l1 u. l2 ) /\ T = ( u1 u. u2 ) )
                                /\
                                S = ( n1 u. n2 )
                              )
                            )
                    )
            )
        )
    )
    \/
    (
      ( NTP4VCEvalUnbound G ( NTP4VCCompose H P I K A ) B )
      /\
      ( ( V = (/) /\ T = { A } ) /\ S = (/) )
    )
  ) $.
$}

ntp4vc-while-results-definition $a |- (
  NTP4VCWhileResults A B C D E F G H I J K L M N O P Q R
) <-> (
  (
    NTP4VCWhileBundle A B C D E F G H I J K L M N O P Q
    ->
    ( NTP4VCBundle A B C D E R G H I J K L N O P Q M )
  )
) $.

${
  $d e p q x A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-command-obligations-definition $a |- (
    NTP4VCCommandObligations
      A B C D E F G H I J K L M N O P Q R S T U V W
  ) <-> (
    (
      (
        B = C
        ->
        T.
      )
      /\
      A. x e. D A. e e. E
        (
          B = ( F ` <. x , e >. )
          ->
          (
            NTP4VCAssignObligation
              A e x G H I J K L M N O P Q R S T U V W
          )
        )
    )
    /\
    (
      A. p e. I A. q e. I
        (
          B = ( J ` <. p , q >. )
          ->
          (
            NTP4VCSeqObligation
              B p q A G D E K L M N O P Q R S T U V
          )
        )
      /\
      (
        A. e e. E A. p e. I A. q e. I
          (
            B = ( K ` <. e , <. p , q >. >. )
            ->
            (
              NTP4VCIfObligation
                A G B p q H D L M N O P Q R S T U V W
              )
            )
          )
        /\
        A. e e. E A. p e. I
          (
            B = ( L ` <. e , p >. )
            ->
            ( NTP4VCWhileObligation B e p D E I J K L G )
          )
      )
    )
  ) $.
$}

${
  $d e l n p q u x A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-command-results-definition $a |- (
    NTP4VCCommandResults
      A B C D E F G H I J K L M N O P Q R S T U V W
  ) <-> (
    A. n e. ( NTP4VCFiniteSubsets H )
      A. u e. ( NTP4VCFiniteSubsets H )
        A. l e. ( NTP4VCFiniteSubsets H )
          (
            (
              B = C
              ->
              ( ( l = (/) /\ u = (/) ) /\ n = { A } )
            )
            /\
            (
              (
                A. x e. D A. e e. E
                  (
                    B = ( F ` <. x , e >. )
                    ->
                    (
                      NTP4VCAssignResults
                        A e x l u n I J K L M N O P Q R S T U V W
                    )
                  )
              )
              /\
              (
                A. p e. G A. q e. G
                  (
                    B = ( J ` <. p , q >. )
                    ->
                    (
                      NTP4VCSeqResults
                        n p q G A K L M N O P u l Q R S T U V W
                    )
                  )
                /\
                (
                  A. e e. E A. p e. G A. q e. G
                    (
                      B = ( K ` <. e , <. p , q >. >. )
                      ->
                      (
                        NTP4VCIfResults
                          A e p q G H I J L M N O P Q R S n u l T U V W
                      )
                    )
                  /\
                  A. e e. E A. p e. G
                    (
                      B = ( L ` <. e , p >. )
                      ->
                      (
                        NTP4VCWhileResults
                          A n u l I e p D M N O P Q R S T U B
                      )
                    )
                )
              )
            )
          )
  ) $.
$}

${
  [ Arbitrary inhabited source carriers. ]
  ntp4vc-program-var-carrier-nonempty $e |- C =/= (/) $.
  ntp4vc-expr-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-svar-carrier-nonempty $e |- E =/= (/) $.
  ntp4vc-symbolic-expr-carrier-nonempty $e |- F =/= (/) $.
  ntp4vc-constraint-carrier-nonempty $e |- G =/= (/) $.
  ntp4vc-model-carrier-nonempty $e |- H =/= (/) $.
  ntp4vc-command-carrier-nonempty $e |- I =/= (/) $.
  ntp4vc-config-carrier-nonempty $e |- J =/= (/) $.
  ntp4vc-state-carrier-nonempty $e |- K =/= (/) $.

  [ The theorem parameters and fact0. ]
  ntp4vc-n-integer $e |- A e. ZZ $.
  ntp4vc-c-command $e |- B e. I $.
  ntp4vc-s-state $e |- L e. K $.
  ntp4vc-fact0 $e |- 0 <_ A $.

  [ Exact command constructors and their exhaustive tagged source carrier. ]
  ntp4vc-cskip-command $e |- M e. I $.
  ntp4vc-cassign-function $e |- N e. ( I ^m ( C X. D ) ) $.
  ntp4vc-cseq-function $e |- O e. ( I ^m ( I X. I ) ) $.
  ntp4vc-cif-function $e |- P e. ( I ^m ( D X. ( I X. I ) ) ) $.
  ntp4vc-cwhile-function $e |- Q e. ( I ^m ( D X. I ) ) $.
  ntp4vc-command-cases $e |- I = (
    { M }
    u.
    (
      ran N
      u.
      ( ran O u. ( ran P u. ran Q ) )
    )
  ) $.

  [ State projections, model operations, constructors, and semantic graphs. ]
  ntp4vc-rho-function $e |- R e. ( ( ZZ ^m E ) ^m K ) $.
  ntp4vc-sigma-function $e |- S e. ( H ^m K ) $.
  ntp4vc-constr-function $e |- T e. ( G ^m K ) $.
  ntp4vc-vars-function
    $e |- U e. ( ( NTP4VCFiniteSubsets E ) ^m K ) $.
  ntp4vc-get-function
    $e |- V e. ( ( NTP4VCOption E ) ^m ( H X. C ) ) $.
  ntp4vc-set-function
    $e |- W e. ( H ^m ( H X. ( C X. E ) ) ) $.

  ntp4vc-interp-function $e |- X e. ( ( ZZ ^m E ) ^m ( ( ZZ ^m E ) X. F ) ) $.
  ntp4vc-symbolic-vars-function
    $e |- Y e. ( ( NTP4VCFiniteSubsets E ) ^m F ) $.
  ntp4vc-constraint-vars-function
    $e |- Z e. ( ( NTP4VCFiniteSubsets E ) ^m G ) $.

  ntp4vc-slit-function $e |- a e. ( F ^m ZZ ) $.
  ntp4vc-svar-function $e |- b e. ( F ^m E ) $.
  ntp4vc-ceq-function $e |- c e. ( G ^m ( F X. F ) ) $.
  ntp4vc-cneq-function $e |- d e. ( G ^m ( F X. F ) ) $.
  ntp4vc-cconj-function $e |- f e. ( G ^m ( G X. G ) ) $.
  ntp4vc-cexists-function $e |- h e. ( G ^m ( E X. G ) ) $.

  ntp4vc-solution-relation $e |- i C_ ( ( ZZ ^m E ) X. G ) $.
  ntp4vc-eval-relation $e |- j C_
    (
      (
        ( ( NTP4VCOption ZZ ) ^m C )
        X.
        D
      )
      X.
      ( ( { 0 } X. ZZ ) u. { <. 1 , 0 >. } )
    ) $.
  ntp4vc-exec-relation $e |- k C_
    (
      (
        (
          (
            J X. ( ( NTP4VCOption ZZ ) ^m C )
          )
          X.
          I
        )
        X.
        ( ( NTP4VCOption ZZ ) ^m C )
      )
      X.
      { 0 , 1 , 2 }
    ) $.
  ntp4vc-exec-while-relation $e |- l C_
    (
      (
        (
          (
            (
              (
                J X. ZZ
              )
              X.
              ( ( NTP4VCOption ZZ ) ^m C )
            )
            X.
            D
          )
          X.
          I
        )
        X.
        ( ( NTP4VCOption ZZ ) ^m C )
      )
      X.
      3
    ) $.
  ntp4vc-mk-loop-cnf-function $e |- m e. ( J ^m ZZ ) $.

  ntp4vc-state-invariant $e |- A. s e. K
    ( NTP4VCStateValid C ( S ` s ) ( U ` s ) E Z V ) $.

  ntp4vc-pearl-imp-symbolic-interpreter-symbolic-interp-cmd-vc
    $a |- (
      (
        NTP4VCCommandObligations
          L B M C D N I O P Q A E F G H J K R S T U V W
      )
      /\
      (
        NTP4VCCommandResults
          L B M C D N I K A j R S T U V k m i Z X Y
      )
    ) $.
$}
$)

${
  ntp4vc-program-var-carrier-nonempty-v2 $e |- C =/= (/) $.
  ntp4vc-expr-carrier-nonempty-v2 $e |- D =/= (/) $.
  ntp4vc-svar-carrier-nonempty-v2 $e |- E =/= (/) $.
  ntp4vc-symbolic-expr-carrier-nonempty-v2 $e |- F =/= (/) $.
  ntp4vc-constraint-carrier-nonempty-v2 $e |- G =/= (/) $.
  ntp4vc-model-carrier-nonempty-v2 $e |- H =/= (/) $.
  ntp4vc-command-carrier-nonempty-v2 $e |- I =/= (/) $.
  ntp4vc-config-carrier-nonempty-v2 $e |- J =/= (/) $.
  ntp4vc-state-carrier-nonempty-v2 $e |- K =/= (/) $.

  ntp4vc-n-integer-v2 $e |- A e. ZZ $.
  ntp4vc-c-command-v2 $e |- B e. I $.
  ntp4vc-s-state-v2 $e |- L e. K $.
  ntp4vc-fact0-v2 $e |- 0 <_ A $.

  ntp4vc-cskip-command-v2 $e |- M e. I $.
  ntp4vc-cassign-function-v2 $e |- N e. ( I ^m ( C X. D ) ) $.
  ntp4vc-cseq-function-v2 $e |- O e. ( I ^m ( I X. I ) ) $.
  ntp4vc-cif-function-v2 $e |- P e. ( I ^m ( D X. ( I X. I ) ) ) $.
  ntp4vc-cwhile-function-v2 $e |- Q e. ( I ^m ( D X. I ) ) $.
  ntp4vc-command-cases-v2 $e |- I = (
    { M } u. ( ran N u. ( ran O u. ( ran P u. ran Q ) ) )
  ) $.

  ntp4vc-cskip-not-assign $e |- -. M e. ran N $.
  ntp4vc-cskip-not-seq $e |- -. M e. ran O $.
  ntp4vc-cskip-not-if $e |- -. M e. ran P $.
  ntp4vc-cskip-not-while $e |- -. M e. ran Q $.
  ntp4vc-assign-seq-disjoint $e |- ( ran N i^i ran O ) = (/) $.
  ntp4vc-assign-if-disjoint $e |- ( ran N i^i ran P ) = (/) $.
  ntp4vc-assign-while-disjoint $e |- ( ran N i^i ran Q ) = (/) $.
  ntp4vc-seq-if-disjoint $e |- ( ran O i^i ran P ) = (/) $.
  ntp4vc-seq-while-disjoint $e |- ( ran O i^i ran Q ) = (/) $.
  ntp4vc-if-while-disjoint $e |- ( ran P i^i ran Q ) = (/) $.

  ntp4vc-cassign-injective $e |- A. x e. C A. y e. D
    A. p e. C A. q e. D
      (
        ( N ` <. x , y >. ) = ( N ` <. p , q >. )
        ->
        ( x = p /\ y = q )
      ) $.
  ntp4vc-cseq-injective $e |- A. x e. I A. y e. I
    A. p e. I A. q e. I
      (
        ( O ` <. x , y >. ) = ( O ` <. p , q >. )
        ->
        ( x = p /\ y = q )
      ) $.
  ntp4vc-cif-injective $e |- A. e e. D A. x e. I A. y e. I
    A. f e. D A. p e. I A. q e. I
      (
        ( P ` <. e , <. x , y >. >. )
          =
        ( P ` <. f , <. p , q >. >. )
        ->
        ( e = f /\ ( x = p /\ y = q ) )
      ) $.
  ntp4vc-cwhile-injective $e |- A. e e. D A. x e. I
    A. f e. D A. p e. I
      (
        ( Q ` <. e , x >. ) = ( Q ` <. f , p >. )
        ->
        ( e = f /\ x = p )
      ) $.

  ntp4vc-command-structural-induction $e |- A. w e. ~P I
    (
      (
        M e. w
        /\
        A. x e. C A. e e. D ( N ` <. x , e >. ) e. w
        /\
        A. p e. I A. q e. I
          (
            ( p e. w /\ q e. w )
            ->
            ( O ` <. p , q >. ) e. w
          )
        /\
        A. e e. D A. p e. I A. q e. I
          (
            ( p e. w /\ q e. w )
            ->
            ( P ` <. e , <. p , q >. >. ) e. w
          )
        /\
        A. e e. D A. p e. I
          (
            p e. w
            ->
            ( Q ` <. e , p >. ) e. w
          )
      )
      ->
      w = I
    ) $.

  ntp4vc-rho-function-v2 $e |- R e. ( ( ZZ ^m E ) ^m K ) $.
  ntp4vc-sigma-function-v2 $e |- S e. ( H ^m K ) $.
  ntp4vc-constr-function-v2 $e |- T e. ( G ^m K ) $.
  ntp4vc-vars-function-v2
    $e |- U e. ( ( NTP4VCFiniteSubsets E ) ^m K ) $.
  ntp4vc-get-function-v2
    $e |- V e. ( ( NTP4VCOption E ) ^m ( H X. C ) ) $.
  ntp4vc-set-function-v2
    $e |- W e. ( H ^m ( H X. ( C X. E ) ) ) $.
  ntp4vc-interp-function-v2
    $e |- X e. ( ( ZZ ^m F ) ^m ( ZZ ^m E ) ) $.
  ntp4vc-symbolic-vars-function-v2
    $e |- Y e. ( ( NTP4VCFiniteSubsets E ) ^m F ) $.
  ntp4vc-constraint-vars-function-v2
    $e |- Z e. ( ( NTP4VCFiniteSubsets E ) ^m G ) $.

  ntp4vc-slit-function-v2 $e |- a e. ( F ^m ZZ ) $.
  ntp4vc-svar-function-v2 $e |- b e. ( F ^m E ) $.
  ntp4vc-ceq-function-v2 $e |- c e. ( G ^m ( F X. F ) ) $.
  ntp4vc-cneq-function-v2 $e |- d e. ( G ^m ( F X. F ) ) $.
  ntp4vc-cconj-function-v2 $e |- f e. ( G ^m ( G X. G ) ) $.
  ntp4vc-cexists-function-v2 $e |- h e. ( G ^m ( E X. G ) ) $.

  ntp4vc-solution-relation-v2 $e |- i C_ ( ( ZZ ^m E ) X. G ) $.
  ntp4vc-eval-relation-v2 $e |- j C_
    (
      ( ( ( NTP4VCOption ZZ ) ^m C ) X. D )
      X.
      ( ( { 0 } X. ZZ ) u. { <. 1 , 0 >. } )
    ) $.
  ntp4vc-exec-relation-v2 $e |- k C_
    (
      ( ( ( J X. ( ( NTP4VCOption ZZ ) ^m C ) ) X. I )
        X. ( ( NTP4VCOption ZZ ) ^m C ) )
      X.
      3
    ) $.
  ntp4vc-exec-while-relation-v2 $e |- l C_
    (
      ( ( ( ( ( J X. ZZ ) X. ( ( NTP4VCOption ZZ ) ^m C ) ) X. D )
          X. I )
        X. ( ( NTP4VCOption ZZ ) ^m C ) )
      X.
      3
    ) $.
  ntp4vc-mk-loop-cnf-function-v2 $e |- m e. ( J ^m ZZ ) $.

  ntp4vc-context-0 $e |- ( z ` 0 ) = C $.
  ntp4vc-context-1 $e |- ( z ` 1 ) = D $.
  ntp4vc-context-2 $e |- ( z ` 2 ) = E $.
  ntp4vc-context-3 $e |- ( z ` 3 ) = F $.
  ntp4vc-context-4 $e |- ( z ` 4 ) = G $.
  ntp4vc-context-5 $e |- ( z ` 5 ) = H $.
  ntp4vc-context-6 $e |- ( z ` 6 ) = I $.
  ntp4vc-context-7 $e |- ( z ` 7 ) = J $.
  ntp4vc-context-8 $e |- ( z ` 8 ) = K $.
  ntp4vc-context-9 $e |- ( z ` 9 ) = M $.
  ntp4vc-context-10 $e |- ( z ` 10 ) = N $.
  ntp4vc-context-11 $e |- ( z ` 11 ) = O $.
  ntp4vc-context-12 $e |- ( z ` 12 ) = P $.
  ntp4vc-context-13 $e |- ( z ` 13 ) = Q $.
  ntp4vc-context-14 $e |- ( z ` 14 ) = R $.
  ntp4vc-context-15 $e |- ( z ` 15 ) = S $.
  ntp4vc-context-16 $e |- ( z ` 16 ) = T $.
  ntp4vc-context-17 $e |- ( z ` 17 ) = U $.
  ntp4vc-context-18 $e |- ( z ` 18 ) = V $.
  ntp4vc-context-19 $e |- ( z ` 19 ) = W $.
  ntp4vc-context-20 $e |- ( z ` 20 ) = X $.
  ntp4vc-context-21 $e |- ( z ` 21 ) = Y $.
  ntp4vc-context-22 $e |- ( z ` 22 ) = Z $.
  ntp4vc-context-23 $e |- ( z ` 23 ) = a $.
  ntp4vc-context-24 $e |- ( z ` 24 ) = b $.
  ntp4vc-context-25 $e |- ( z ` 25 ) = c $.
  ntp4vc-context-26 $e |- ( z ` 26 ) = d $.
  ntp4vc-context-27 $e |- ( z ` 27 ) = f $.
  ntp4vc-context-28 $e |- ( z ` 28 ) = h $.
  ntp4vc-context-29 $e |- ( z ` 29 ) = i $.
  ntp4vc-context-30 $e |- ( z ` 30 ) = j $.
  ntp4vc-context-31 $e |- ( z ` 31 ) = k $.
  ntp4vc-context-32 $e |- ( z ` 32 ) = l $.
  ntp4vc-context-33 $e |- ( z ` 33 ) = m $.
  ntp4vc-context-34 $e |- ( z ` 34 ) = A $.
  ntp4vc-context-35 $e |- ( z ` 35 ) = B $.
  ntp4vc-context-36 $e |- ( z ` 36 ) = L $.

  ntp4vc-state-invariant-v2 $e |- A. s e. K
    ( NTP4VCCtxStateValid z ( S ` s ) ( T ` s ) ( U ` s ) ) $.
  ntp4vc-state-extensionality $e |- A. s e. K A. t e. K
    (
      (
        ( S ` s ) = ( S ` t )
        /\
        ( T ` s ) = ( T ` t )
        /\
        ( R ` s ) = ( R ` t )
        /\
        ( U ` s ) = ( U ` t )
      )
      ->
      s = t
    ) $.
  ntp4vc-state-construction $e |- A. o e. H A. g e. G
    A. r e. ( ZZ ^m E ) A. u e. ( NTP4VCFiniteSubsets E )
      (
        ( NTP4VCCtxStateValid z o g u )
        ->
        E. s e. K
          (
            ( S ` s ) = o
            /\
            ( T ` s ) = g
            /\
            ( R ` s ) = r
            /\
            ( U ` s ) = u
          )
      ) $.

  ntp4vc-pearl-imp-symbolic-interpreter-symbolic-interp-cmd-vc-v2
    $a |- ( NTP4VCStatement z ) $.
$}
