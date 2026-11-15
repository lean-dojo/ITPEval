$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmd_listqtvc: the
  symbolic-command interpreter combines the execution results for the head
  and tail of a list of symbolic states while preserving state extension,
  solution, concrete-execution, and behavior-partition specifications. This
  file contains no proof.
$)

$[ lib/set.mm $]

$v ntpc1 ntpc2 ntpe2 ntpenv ntpenv1 ntpenv2 ntpenv3
   ntpcnf ntpctr ntpz2 ntpn2 $.
ntp4vc-f-ntpc1 $f class ntpc1 $.
ntp4vc-f-ntpc2 $f class ntpc2 $.
ntp4vc-f-ntpe2 $f class ntpe2 $.
ntp4vc-f-ntpenv $f class ntpenv $.
ntp4vc-f-ntpenv1 $f class ntpenv1 $.
ntp4vc-f-ntpenv2 $f class ntpenv2 $.
ntp4vc-f-ntpenv3 $f class ntpenv3 $.
ntp4vc-f-ntpcnf $f class ntpcnf $.
ntp4vc-f-ntpctr $f class ntpctr $.
ntp4vc-f-ntpz2 $f class ntpz2 $.
ntp4vc-f-ntpn2 $f class ntpn2 $.

$(
  NTP4VCPVar, NTP4VCSVar, NTP4VCModel (source Constraint.t), and
  NTP4VCSVarSet (source Svar.set) are fixed inhabited set carriers. The last
  two remain opaque: NTP4VCGet and NTP4VCToFSet are fixed source operations,
  so distinct carrier values with identical observable projections are not
  identified. Symbolic states are invariant four-tuples over those carriers.
  Expressions, commands, symbolic expressions, constraints, configurations,
  the recursive solution predicate, and the mutually inductive command/while
  execution relation are defined below in SetMM. Tagged ordered pairs give
  constructor-disjoint inductive datatypes, and intersections of all closed
  classes give their least inductive semantics.

  Source SymStateSet wrappers are replaced only by their observable to_fset
  values. The source mk specification makes to_fset surjective onto all finite
  subsets, while every occurrence in this VC is extensional in to_fset, so
  quantification over finite subsets of NTP4VCState is equivalent in both
  directions
  to quantification over wrappers. The range of a SetMM word is exactly the
  finite set represented by SymStateSet.to_fset (of_list ss).

  NTP4VCStateExtends, NTP4VCResultsExtend, NTP4VCForward,
  NTP4VCBackward, NTP4VCBundle, NTP4VCConclusion, and NTP4VCStep are direct
  definitional expansions of the corresponding source subformulas. The source
  list matches become the final empty-or-cons disjunction; in the empty case
  the result-set premise forces all three finite sets empty, making every
  conclusion clause vacuous. The only parameters of the final verification
  condition are n, ss, and c. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof.
$)

$c
  NTP4VCOption NTP4VCSome NTP4VCFiniteSubsets NTP4VCCompose
  NTP4VCStateExtends NTP4VCResultsExtend NTP4VCSolution NTP4VCExec
  NTP4VCOutMember NTP4VCForward NTP4VCBackward NTP4VCBundle
  NTP4VCConclusion NTP4VCStep
  NTP4VCPVar NTP4VCSVar NTP4VCModel NTP4VCSVarSet
  NTP4VCModelEmpty NTP4VCModelSet NTP4VCSVarSetMk NTP4VCToFSet
  NTP4VCConstraint NTP4VCExpr
  NTP4VCCmd NTP4VCConfig NTP4VCState NTP4VCRho NTP4VCSigma
  NTP4VCConstrOf NTP4VCVarsOf NTP4VCGet NTP4VCSolutionGraph
  NTP4VCExecCmdGraph NTP4VCExecWhileGraph NTP4VCMkLoop
  NTP4VCConstraintVars NTP4VCLoopLimit
  NTP4VCElit NTP4VCEvar NTP4VCEsub NTP4VCExprClosed
  NTP4VCCskip NTP4VCCassign NTP4VCCseq NTP4VCCif NTP4VCCwhile
  NTP4VCCmdClosed NTP4VCSLit NTP4VCSVarExpr NTP4VCSSub
  NTP4VCSExpr NTP4VCSExprClosed NTP4VCCtrue NTP4VCCfalse
  NTP4VCCeq NTP4VCCneq NTP4VCCconj NTP4VCCexists
  NTP4VCConstraintClosed NTP4VCSEvalClosed NTP4VCSEvalGraph
  NTP4VCSExprVarsClosed NTP4VCSExprVarsGraph
  NTP4VCConstraintVarsClosed NTP4VCConstraintVarsGraph
  NTP4VCSolutionClosed NTP4VCEvalClosed NTP4VCEvalGraph
  NTP4VCEval NTP4VCEnvUpdate NTP4VCExecClosed NTP4VCExecGraph
  NTP4VCInCmd NTP4VCInWhile NTP4VCPermit NTP4VCOverflow
$.

ntp4vc-pvar-source-syntax $a class NTP4VCPVar $.
ntp4vc-svar-source-syntax $a class NTP4VCSVar $.
ntp4vc-model-source-syntax $a class NTP4VCModel $.
ntp4vc-svar-set-source-syntax $a class NTP4VCSVarSet $.
ntp4vc-model-empty-source-syntax $a class NTP4VCModelEmpty $.
ntp4vc-model-set-source-syntax $a class NTP4VCModelSet $.
ntp4vc-svar-set-mk-source-syntax $a class NTP4VCSVarSetMk $.
ntp4vc-to-fset-source-syntax $a class NTP4VCToFSet $.
ntp4vc-constraint-source-syntax $a class NTP4VCConstraint $.
ntp4vc-expr-source-syntax $a class NTP4VCExpr $.
ntp4vc-cmd-source-syntax $a class NTP4VCCmd $.
ntp4vc-config-source-syntax $a class NTP4VCConfig $.
ntp4vc-state-source-syntax $a class NTP4VCState $.
ntp4vc-rho-source-syntax $a class NTP4VCRho $.
ntp4vc-sigma-source-syntax $a class NTP4VCSigma $.
ntp4vc-constr-source-syntax $a class NTP4VCConstrOf $.
ntp4vc-vars-source-syntax $a class NTP4VCVarsOf $.
ntp4vc-get-source-syntax $a class NTP4VCGet $.
ntp4vc-solution-graph-source-syntax $a class NTP4VCSolutionGraph $.
ntp4vc-exec-cmd-graph-source-syntax $a class NTP4VCExecCmdGraph $.
ntp4vc-exec-while-graph-source-syntax $a class NTP4VCExecWhileGraph $.
ntp4vc-mk-loop-source-syntax $a class NTP4VCMkLoop $.
ntp4vc-constraint-vars-source-syntax $a class NTP4VCConstraintVars $.
ntp4vc-loop-limit-source-syntax $a class NTP4VCLoopLimit $.

ntp4vc-elit-syntax $a class ( NTP4VCElit A ) $.
ntp4vc-evar-syntax $a class ( NTP4VCEvar A ) $.
ntp4vc-esub-syntax $a class ( NTP4VCEsub A B ) $.
ntp4vc-expr-closed-syntax $a wff ( NTP4VCExprClosed A ) $.
ntp4vc-cskip-syntax $a class NTP4VCCskip $.
ntp4vc-cassign-syntax $a class ( NTP4VCCassign A B ) $.
ntp4vc-cseq-syntax $a class ( NTP4VCCseq A B ) $.
ntp4vc-cif-syntax $a class ( NTP4VCCif A B C ) $.
ntp4vc-cwhile-syntax $a class ( NTP4VCCwhile A B ) $.
ntp4vc-cmd-closed-syntax $a wff ( NTP4VCCmdClosed A ) $.
ntp4vc-slit-syntax $a class ( NTP4VCSLit A ) $.
ntp4vc-svar-expr-syntax $a class ( NTP4VCSVarExpr A ) $.
ntp4vc-ssub-syntax $a class ( NTP4VCSSub A B ) $.
ntp4vc-sexpr-closed-syntax $a wff ( NTP4VCSExprClosed A ) $.
ntp4vc-ctrue-syntax $a class NTP4VCCtrue $.
ntp4vc-cfalse-syntax $a class NTP4VCCfalse $.
ntp4vc-ceq-syntax $a class ( NTP4VCCeq A B ) $.
ntp4vc-cneq-syntax $a class ( NTP4VCCneq A B ) $.
ntp4vc-cconj-syntax $a class ( NTP4VCCconj A B ) $.
ntp4vc-cexists-syntax $a class ( NTP4VCCexists A B ) $.
ntp4vc-constraint-closed-syntax
  $a wff ( NTP4VCConstraintClosed A ) $.
ntp4vc-seval-closed-syntax $a wff ( NTP4VCSEvalClosed A ) $.
ntp4vc-sexpr-vars-closed-syntax
  $a wff ( NTP4VCSExprVarsClosed A ) $.
ntp4vc-constraint-vars-closed-syntax
  $a wff ( NTP4VCConstraintVarsClosed A ) $.
ntp4vc-solution-closed-syntax $a wff ( NTP4VCSolutionClosed A ) $.
ntp4vc-eval-closed-syntax $a wff ( NTP4VCEvalClosed A ) $.
ntp4vc-eval-syntax $a wff ( NTP4VCEval A B C ) $.
ntp4vc-env-update-syntax $a class ( NTP4VCEnvUpdate A B C ) $.
ntp4vc-exec-closed-syntax $a wff ( NTP4VCExecClosed A ) $.
ntp4vc-in-cmd-syntax
  $a wff ( NTP4VCInCmd A B C D E F ) $.
ntp4vc-in-while-syntax
  $a wff ( NTP4VCInWhile A B C D E F G H ) $.
ntp4vc-permit-syntax $a wff ( NTP4VCPermit A B ) $.
ntp4vc-overflow-syntax $a wff ( NTP4VCOverflow A B ) $.

ntp4vc-option-syntax
  $a class ( NTP4VCOption A ) $.
ntp4vc-some-syntax
  $a class ( NTP4VCSome A ) $.
ntp4vc-finite-subsets-syntax
  $a class ( NTP4VCFiniteSubsets A ) $.
ntp4vc-compose-syntax
  $a class ( NTP4VCCompose A B C D E ) $.

ntp4vc-state-extends-syntax
  $a wff ( NTP4VCStateExtends A B C D ) $.
ntp4vc-results-extend-syntax
  $a wff ( NTP4VCResultsExtend A B C D E F ) $.
ntp4vc-solution-syntax
  $a wff ( NTP4VCSolution A B C D ) $.
ntp4vc-exec-syntax
  $a wff ( NTP4VCExec A B C D E F ) $.
ntp4vc-out-member-syntax
  $a wff ( NTP4VCOutMember A B C D E ) $.
ntp4vc-forward-syntax
  $a wff (
    NTP4VCForward A B C D E F G H I J K L M N O
  ) $.
ntp4vc-backward-syntax
  $a wff (
    NTP4VCBackward A B C D E F G H I J K L M N O
  ) $.
ntp4vc-bundle-syntax
  $a wff (
    NTP4VCBundle A B C D E F G H I J K L M N O P
  ) $.
ntp4vc-conclusion-syntax
  $a wff (
    NTP4VCConclusion A B C D E F G H I J K L M N O P
  ) $.
ntp4vc-step-syntax
  $a wff (
    NTP4VCStep A B C D E F G H I J K L M N O
  ) $.

ntp4vc-option-definition $a |- (
  NTP4VCOption A
) = (
  ( { 0 } X. { 0 } )
  u.
  ( { 1 } X. A )
) $.

ntp4vc-some-definition $a |- (
  NTP4VCSome A
) = <. 1 , A >. $.

ntp4vc-finite-subsets-definition $a |- (
  NTP4VCFiniteSubsets A
) = (
  ( ~P A ) i^i Fin
) $.

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
          (
            ( B ` E )
            `
            ( 2nd ` ( D ` <. ( C ` E ) , x >. ) )
          )
        )
      )
  ) $.
$}

${
  $d v A B C D $.

  ntp4vc-state-extends-definition $a |- (
    NTP4VCStateExtends A B C D
  ) <-> (
    ( C ` A ) C_ ( C ` B )
    /\
    A. v e. ( C ` A )
      (
        ( ( D ` A ) ` v )
        =
        ( ( D ` B ) ` v )
      )
  ) $.
$}

${
  $d s A B C D E F $.

  ntp4vc-results-extend-definition $a |- (
    NTP4VCResultsExtend A B C D E F
  ) <-> (
    A. s e. ( ( B u. C ) u. D )
      ( NTP4VCStateExtends A s E F )
  ) $.
$}

ntp4vc-solution-definition $a |- (
  NTP4VCSolution A B C D
) <-> (
  <. ( B ` D ) , ( C ` D ) >. e. A
) $.

ntp4vc-exec-definition $a |- (
  NTP4VCExec A B C D E F
) <-> (
  <. <. <. <. B , C >. , D >. , E >. , F >. e. A
) $.

ntp4vc-out-member-definition $a |- (
  NTP4VCOutMember A B C D E
) <-> (
  (
    A = 0
    /\
    B e. C
  )
  \/
  (
    (
      A = 1
      /\
      B e. D
    )
    \/
    (
      A = 2
      /\
      B e. E
    )
  )
) $.

${
  $d b g s A B C D E F G H I J K L M N O $.

  $(
    A is the input state; B, C, D are the normal, unbound-variable,
    and loop-limit result sets. E is n, F is c, G is the program-variable
    carrier, H is rho, I is sigma, J is get, K is is_solution, L is constr,
    M is exec_cmd, N is mk_loop_cnf, and O is the symbolic-state carrier.
  $)
  ntp4vc-forward-definition $a |- (
    NTP4VCForward A B C D E F G H I J K L M N O
  ) <-> (
    A. g e. ( ( NTP4VCOption ZZ ) ^m G )
      A. b e. 3
        (
          (
            NTP4VCExec
              M
              ( N ` E )
              ( NTP4VCCompose G H I J A )
              F g b
          )
          ->
          E. s e. O
            (
              ( NTP4VCOutMember b s B C D )
              /\
              (
                ( NTP4VCSolution K H L s )
                /\
                g = ( NTP4VCCompose G H I J s )
              )
            )
        )
  ) $.
$}

${
  $d b s A B C D E F G H I J K L M N O $.

  ntp4vc-backward-definition $a |- (
    NTP4VCBackward A B C D E F G H I J K L M N O
  ) <-> (
    A. b e. 3 A. s e. O
      (
        ( NTP4VCOutMember b s B C D )
        ->
        (
          ( NTP4VCSolution K H L s )
          ->
          (
            ( NTP4VCSolution K H L A )
            /\
            (
              NTP4VCExec
                M
                ( N ` E )
                ( NTP4VCCompose G H I J A )
                F
                ( NTP4VCCompose G H I J s )
                b
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
      (
        NTP4VCForward
          A B C D E F G H I J K L M N O
      )
    )
    /\
    (
      NTP4VCBackward
        A B C D E F G H I J K L M N O
    )
  )
) $.

${
  $d b s t A B C D E F G H I J K L M N O P $.

  $(
    A is a source state list; B, C, D are the three result sets. The remaining
    arguments have the same order as in NTP4VCBundle.
  $)
  ntp4vc-conclusion-definition $a |- (
    NTP4VCConclusion A B C D E F G H I J K L M N O P
  ) <-> (
    (
      A. s e. ( ( B u. C ) u. D )
        E. t e. ran A
          ( NTP4VCStateExtends t s P H )
    )
    /\
    (
      (
        A. t e. ran A
          (
            ( NTP4VCSolution K H L t )
            ->
            (
              NTP4VCForward
                t B C D E F G H I J K L M N O
            )
          )
      )
      /\
      (
        A. b e. 3 A. s e. O
          (
            ( NTP4VCOutMember b s B C D )
            ->
            (
              ( NTP4VCSolution K H L s )
              ->
              E. t e. ran A
                (
                  ( NTP4VCSolution K H L t )
                  /\
                  (
                    NTP4VCExec
                      M
                      ( N ` E )
                      ( NTP4VCCompose G H I J t )
                      F
                      ( NTP4VCCompose G H I J s )
                      b
                  )
                )
            )
          )
      )
    )
  ) $.
$}

${
  $d l l1 n n1 u u1 x y z
     A B C D E F G H I J K L M N O $.

  $(
    A is the whole nonempty list, B its head, and C its tail. D through O are
    n, c, the program-variable carrier, rho, sigma, get, is_solution, constr,
    exec_cmd, mk_loop_cnf, the state carrier, and vars.
  $)
  ntp4vc-step-definition $a |- (
    NTP4VCStep A B C D E F G H I J K L M N O
  ) <-> (
    (
      (
        (
          0 <_ ( # ` A )
          /\
          0 < ( # ` A )
        )
        /\
        0 <_ D
      )
      /\
      A. x e. ( NTP4VCFiniteSubsets N )
        A. y e. ( NTP4VCFiniteSubsets N )
          A. z e. ( NTP4VCFiniteSubsets N )
            (
              (
                NTP4VCBundle
                  B x y z D E F G H I J K L M N O
              )
              ->
              (
                (
                  0 <_ ( # ` A )
                  /\
                  ( # ` C ) < ( # ` A )
                )
                /\
                0 <_ D
              )
            )
    )
    /\
    A. x e. ( NTP4VCFiniteSubsets N )
      A. y e. ( NTP4VCFiniteSubsets N )
        A. z e. ( NTP4VCFiniteSubsets N )
          (
            (
              E. n1 e. ( NTP4VCFiniteSubsets N )
                E. u1 e. ( NTP4VCFiniteSubsets N )
                  E. l1 e. ( NTP4VCFiniteSubsets N )
                    (
                      (
                        NTP4VCBundle
                          B n1 u1 l1 D E F G H I J K L M N O
                      )
                      /\
                      E. n e. ( NTP4VCFiniteSubsets N )
                        E. u e. ( NTP4VCFiniteSubsets N )
                          E. l e. ( NTP4VCFiniteSubsets N )
                            (
                              (
                                NTP4VCConclusion
                                  C n u l D E F G H I J K L M N O
                              )
                              /\
                              (
                                z = ( l1 u. l )
                                /\
                                (
                                  y = ( u1 u. u )
                                  /\
                                  x = ( n1 u. n )
                                )
                              )
                            )
                    )
            )
            ->
            (
              NTP4VCConclusion
                A x y z D E F G H I J K L M N O
            )
          )
  ) $.
$}
$(
  Fixed source theory. Its primitive carriers are explicitly sets and
  inhabited. Constraint.t and Svar.set remain opaque carriers rather than
  being replaced by their observable functions or finite subsets.
$)
ntp4vc-source-pvar-set $a |- NTP4VCPVar e. _V $.
ntp4vc-source-svar-set $a |- NTP4VCSVar e. _V $.
ntp4vc-source-model-set $a |- NTP4VCModel e. _V $.
ntp4vc-source-svar-set-set $a |- NTP4VCSVarSet e. _V $.
ntp4vc-source-pvar-inhabited $a |- NTP4VCPVar =/= (/) $.
ntp4vc-source-svar-inhabited $a |- NTP4VCSVar =/= (/) $.
ntp4vc-source-model-inhabited $a |- NTP4VCModel =/= (/) $.
ntp4vc-source-svar-set-inhabited $a |- NTP4VCSVarSet =/= (/) $.

ntp4vc-elit-definition $a |- ( NTP4VCElit A ) = <. 0 , A >. $.
ntp4vc-evar-definition $a |- ( NTP4VCEvar A ) = <. 1 , A >. $.
ntp4vc-esub-definition $a |- ( NTP4VCEsub A B ) =
  <. 2 , <. A , B >. >. $.

${
  $d e e1 ntpe2 n x A $.
  ntp4vc-expr-closed-definition $a |- (
    NTP4VCExprClosed A
  ) <-> (
    (
      A. n e. ZZ ( NTP4VCElit n ) e. A
      /\
      A. x e. NTP4VCPVar ( NTP4VCEvar x ) e. A
    )
    /\
    A. e1 e. A A. ntpe2 e. A ( NTP4VCEsub e1 ntpe2 ) e. A
  ) $.
$}
ntp4vc-expr-definition $a |- NTP4VCExpr =
  |^| { x | ( NTP4VCExprClosed x ) } $.

ntp4vc-cskip-definition $a |- NTP4VCCskip = <. 0 , 0 >. $.
ntp4vc-cassign-definition $a |- ( NTP4VCCassign A B ) =
  <. 1 , <. A , B >. >. $.
ntp4vc-cseq-definition $a |- ( NTP4VCCseq A B ) =
  <. 2 , <. A , B >. >. $.
ntp4vc-cif-definition $a |- ( NTP4VCCif A B C ) =
  <. 3 , <. A , <. B , C >. >. >. $.
ntp4vc-cwhile-definition $a |- ( NTP4VCCwhile A B ) =
  <. 4 , <. A , B >. >. $.

${
  $d c ntpc1 ntpc2 e v A $.
  ntp4vc-cmd-closed-definition $a |- (
    NTP4VCCmdClosed A
  ) <-> (
    (
      NTP4VCCskip e. A
      /\
      A. v e. NTP4VCPVar A. e e. NTP4VCExpr
        ( NTP4VCCassign v e ) e. A
    )
    /\
    (
      A. ntpc1 e. A A. ntpc2 e. A ( NTP4VCCseq ntpc1 ntpc2 ) e. A
      /\
      (
        A. e e. NTP4VCExpr A. ntpc1 e. A A. ntpc2 e. A
          ( NTP4VCCif e ntpc1 ntpc2 ) e. A
        /\
        A. e e. NTP4VCExpr A. c e. A
          ( NTP4VCCwhile e c ) e. A
      )
    )
  ) $.
$}
ntp4vc-cmd-definition $a |- NTP4VCCmd =
  |^| { x | ( NTP4VCCmdClosed x ) } $.

ntp4vc-slit-definition $a |- ( NTP4VCSLit A ) = <. 0 , A >. $.
ntp4vc-svar-expr-definition $a |- ( NTP4VCSVarExpr A ) =
  <. 1 , A >. $.
ntp4vc-ssub-definition $a |- ( NTP4VCSSub A B ) =
  <. 2 , <. A , B >. >. $.

${
  $d e1 ntpe2 n v A $.
  ntp4vc-sexpr-closed-definition $a |- (
    NTP4VCSExprClosed A
  ) <-> (
    (
      A. n e. ZZ ( NTP4VCSLit n ) e. A
      /\
      A. v e. NTP4VCSVar ( NTP4VCSVarExpr v ) e. A
    )
    /\
    A. e1 e. A A. ntpe2 e. A ( NTP4VCSSub e1 ntpe2 ) e. A
  ) $.
$}
ntp4vc-sexpr-definition $a |- NTP4VCSExpr =
  |^| { x | ( NTP4VCSExprClosed x ) } $.

ntp4vc-ctrue-definition $a |- NTP4VCCtrue = <. 0 , 0 >. $.
ntp4vc-cfalse-definition $a |- NTP4VCCfalse = <. 1 , 0 >. $.
ntp4vc-ceq-definition $a |- ( NTP4VCCeq A B ) =
  <. 2 , <. A , B >. >. $.
ntp4vc-cneq-definition $a |- ( NTP4VCCneq A B ) =
  <. 3 , <. A , B >. >. $.
ntp4vc-cconj-definition $a |- ( NTP4VCCconj A B ) =
  <. 4 , <. A , B >. >. $.
ntp4vc-cexists-definition $a |- ( NTP4VCCexists A B ) =
  <. 5 , <. A , B >. >. $.

${
  $d ntpc1 ntpc2 e1 ntpe2 v A $.
  ntp4vc-constraint-closed-definition $a |- (
    NTP4VCConstraintClosed A
  ) <-> (
    (
      ( NTP4VCCtrue e. A /\ NTP4VCCfalse e. A )
      /\
      A. e1 e. NTP4VCSExpr A. ntpe2 e. NTP4VCSExpr
        (
          ( NTP4VCCeq e1 ntpe2 ) e. A
          /\
          ( NTP4VCCneq e1 ntpe2 ) e. A
        )
    )
    /\
    (
      A. ntpc1 e. A A. ntpc2 e. A ( NTP4VCCconj ntpc1 ntpc2 ) e. A
      /\
      A. v e. NTP4VCSVar A. ntpc1 e. A
        ( NTP4VCCexists v ntpc1 ) e. A
    )
  ) $.
$}
ntp4vc-constraint-definition $a |- NTP4VCConstraint =
  |^| { x | ( NTP4VCConstraintClosed x ) } $.

${
  $d e1 ntpe2 n r v z z1 ntpz2 A $.
  ntp4vc-seval-closed-definition $a |- (
    NTP4VCSEvalClosed A
  ) <-> (
    (
      A. r e. ( ZZ ^m NTP4VCSVar ) A. n e. ZZ
        <. r , <. ( NTP4VCSLit n ) , n >. >. e. A
      /\
      A. r e. ( ZZ ^m NTP4VCSVar ) A. v e. NTP4VCSVar
        <. r , <. ( NTP4VCSVarExpr v ) , ( r ` v ) >. >. e. A
    )
    /\
    A. r e. ( ZZ ^m NTP4VCSVar )
      A. e1 e. NTP4VCSExpr A. ntpe2 e. NTP4VCSExpr
        A. z1 e. ZZ A. ntpz2 e. ZZ
          (
            (
              <. r , <. e1 , z1 >. >. e. A
              /\
              <. r , <. ntpe2 , ntpz2 >. >. e. A
            )
            ->
            <. r , <. ( NTP4VCSSub e1 ntpe2 ) ,
              ( z1 - ntpz2 ) >. >. e. A
          )
  ) $.
$}
ntp4vc-seval-graph-definition $a |- NTP4VCSEvalGraph =
  |^| { x | ( NTP4VCSEvalClosed x ) } $.

${
  $d e1 ntpe2 v A $.
  ntp4vc-sexpr-vars-closed-definition $a |- (
    NTP4VCSExprVarsClosed A
  ) <-> (
    A. v e. NTP4VCSVar
      <. ( NTP4VCSVarExpr v ) , v >. e. A
    /\
    A. e1 e. NTP4VCSExpr A. ntpe2 e. NTP4VCSExpr A. v e. NTP4VCSVar
      (
        (
          <. e1 , v >. e. A
          \/
          <. ntpe2 , v >. e. A
        )
        ->
        <. ( NTP4VCSSub e1 ntpe2 ) , v >. e. A
      )
  ) $.
$}
ntp4vc-sexpr-vars-graph-definition $a |- NTP4VCSExprVarsGraph =
  |^| { x | ( NTP4VCSExprVarsClosed x ) } $.

${
  $d c ntpc1 ntpc2 e1 ntpe2 v w A $.
  ntp4vc-constraint-vars-closed-definition $a |- (
    NTP4VCConstraintVarsClosed A
  ) <-> (
    (
      A. e1 e. NTP4VCSExpr A. ntpe2 e. NTP4VCSExpr
        A. v e. NTP4VCSVar
          (
            (
              <. e1 , v >. e. NTP4VCSExprVarsGraph
              \/
              <. ntpe2 , v >. e. NTP4VCSExprVarsGraph
            )
            ->
            (
              <. ( NTP4VCCeq e1 ntpe2 ) , v >. e. A
              /\
              <. ( NTP4VCCneq e1 ntpe2 ) , v >. e. A
            )
          )
      /\
      A. ntpc1 e. NTP4VCConstraint A. ntpc2 e. NTP4VCConstraint
        A. v e. NTP4VCSVar
          (
            (
              <. ntpc1 , v >. e. A
              \/
              <. ntpc2 , v >. e. A
            )
            ->
            <. ( NTP4VCCconj ntpc1 ntpc2 ) , v >. e. A
          )
    )
    /\
    A. w e. NTP4VCSVar A. c e. NTP4VCConstraint
      A. v e. NTP4VCSVar
        (
          (
            v = w
            \/
            <. c , v >. e. A
          )
          ->
          <. ( NTP4VCCexists w c ) , v >. e. A
        )
  ) $.
$}
ntp4vc-constraint-vars-graph-definition
  $a |- NTP4VCConstraintVarsGraph =
    |^| { x | ( NTP4VCConstraintVarsClosed x ) } $.

${
  $d c v $.
  ntp4vc-constraint-vars-definition $a |- NTP4VCConstraintVars =
    ( c e. NTP4VCConstraint |->
      { v e. NTP4VCSVar |
        <. c , v >. e. NTP4VCConstraintVarsGraph } ) $.
$}

${
  $d c ntpc1 ntpc2 e1 ntpe2 r v z z1 ntpz2 A $.
  ntp4vc-solution-closed-definition $a |- (
    NTP4VCSolutionClosed A
  ) <-> (
    (
      A. r e. ( ZZ ^m NTP4VCSVar )
        <. r , NTP4VCCtrue >. e. A
      /\
      A. r e. ( ZZ ^m NTP4VCSVar )
        A. e1 e. NTP4VCSExpr A. ntpe2 e. NTP4VCSExpr
          (
            (
              E. z e. ZZ
                (
                  <. r , <. e1 , z >. >. e. NTP4VCSEvalGraph
                  /\
                  <. r , <. ntpe2 , z >. >. e. NTP4VCSEvalGraph
                )
              ->
              <. r , ( NTP4VCCeq e1 ntpe2 ) >. e. A
            )
            /\
            (
              E. z1 e. ZZ E. ntpz2 e. ZZ
                (
                  (
                    <. r , <. e1 , z1 >. >. e. NTP4VCSEvalGraph
                    /\
                    <. r , <. ntpe2 , ntpz2 >. >. e. NTP4VCSEvalGraph
                  )
                  /\
                  z1 =/= ntpz2
                )
              ->
              <. r , ( NTP4VCCneq e1 ntpe2 ) >. e. A
            )
          )
    )
    /\
    (
      A. r e. ( ZZ ^m NTP4VCSVar )
        A. ntpc1 e. NTP4VCConstraint A. ntpc2 e. NTP4VCConstraint
          (
            (
              <. r , ntpc1 >. e. A
              /\
              <. r , ntpc2 >. e. A
            )
            ->
            <. r , ( NTP4VCCconj ntpc1 ntpc2 ) >. e. A
          )
      /\
      A. r e. ( ZZ ^m NTP4VCSVar )
        A. v e. NTP4VCSVar A. c e. NTP4VCConstraint
          (
            <. r , c >. e. A
            ->
            <. r , ( NTP4VCCexists v c ) >. e. A
          )
    )
  ) $.
$}
ntp4vc-solution-graph-definition $a |- NTP4VCSolutionGraph =
  |^| { x | ( NTP4VCSolutionClosed x ) } $.

$(
  Faithful opaque Constraint.t interface. The update axioms constrain its
  fixed lookup operation without identifying model values extensionally.
$)
ntp4vc-get-type $a |- NTP4VCGet e.
  ( ( NTP4VCOption NTP4VCSVar ) ^m
    ( NTP4VCModel X. NTP4VCPVar ) ) $.
ntp4vc-model-empty-type $a |- NTP4VCModelEmpty e. NTP4VCModel $.
ntp4vc-model-set-type $a |- NTP4VCModelSet e.
  ( NTP4VCModel ^m
    ( ( NTP4VCModel X. NTP4VCPVar ) X. NTP4VCSVar ) ) $.
${
  ntp4vc-model-empty-spec $a |- A. k e. NTP4VCPVar
    ( NTP4VCGet ` <. NTP4VCModelEmpty , k >. ) = <. 0 , 0 >. $.
$}
${
  $d d k v $.
  ntp4vc-model-set-here-spec $a |-
    A. d e. NTP4VCModel A. k e. NTP4VCPVar A. v e. NTP4VCSVar
      ( NTP4VCGet `
        <. ( NTP4VCModelSet ` <. <. d , k >. , v >. ) , k >. )
      = ( NTP4VCSome v ) $.
$}
${
  $d d k v x $.
  ntp4vc-model-set-away-spec $a |-
    A. d e. NTP4VCModel A. k e. NTP4VCPVar A. v e. NTP4VCSVar
      A. x e. NTP4VCPVar
        ( x =/= k ->
          ( NTP4VCGet `
            <. ( NTP4VCModelSet ` <. <. d , k >. , v >. ) , x >. )
          = ( NTP4VCGet ` <. d , x >. ) ) $.
$}

$(
  Faithful opaque Svar.set interface. Its constructor witnesses surjectivity
  of to_fset, but wrappers with the same finite image remain distinct.
$)
ntp4vc-to-fset-type $a |- NTP4VCToFSet e.
  ( ( NTP4VCFiniteSubsets NTP4VCSVar ) ^m NTP4VCSVarSet ) $.
ntp4vc-svar-set-mk-type $a |- NTP4VCSVarSetMk e.
  ( NTP4VCSVarSet ^m ( NTP4VCFiniteSubsets NTP4VCSVar ) ) $.
${
  ntp4vc-svar-set-mk-spec $a |-
    A. f e. ( NTP4VCFiniteSubsets NTP4VCSVar )
      ( NTP4VCToFSet ` ( NTP4VCSVarSetMk ` f ) ) = f $.
$}

ntp4vc-config-definition $a |- NTP4VCConfig =
  { q e. ( NTP4VCOption ZZ ) |
    (
      ( 1st ` q ) = 0
      \/
      (
        ( 1st ` q ) = 1
        /\
        0 <_ ( 2nd ` q )
      )
    ) } $.
ntp4vc-loop-limit-definition $a |- NTP4VCLoopLimit =
  ( q e. NTP4VCConfig |-> q ) $.
ntp4vc-mk-loop-definition $a |- NTP4VCMkLoop =
  ( n e. ZZ |->
    if ( 0 <_ n , ( NTP4VCSome n ) , <. 0 , 0 >. ) ) $.

${
  $d e e1 ntpe2 ntpenv n n1 ntpn2 v A $.
  ntp4vc-eval-closed-definition $a |- (
    NTP4VCEvalClosed A
  ) <-> (
    (
      A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
        A. n e. ZZ
          <. ntpenv , <. ( NTP4VCElit n ) , <. 0 , n >. >. >. e. A
      /\
      (
        A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
          A. v e. NTP4VCPVar A. n e. ZZ
            (
              ( ntpenv ` v ) = ( NTP4VCSome n )
              ->
              <. ntpenv , <. ( NTP4VCEvar v ) ,
                <. 0 , n >. >. >. e. A
            )
        /\
        A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
          A. v e. NTP4VCPVar
            (
              ( ntpenv ` v ) = <. 0 , 0 >.
              ->
              <. ntpenv , <. ( NTP4VCEvar v ) ,
                <. 1 , 0 >. >. >. e. A
            )
      )
    )
    /\
    (
      A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
        A. e1 e. NTP4VCExpr A. ntpe2 e. NTP4VCExpr
          A. n1 e. ZZ A. ntpn2 e. ZZ
            (
              (
                <. ntpenv , <. e1 , <. 0 , n1 >. >. >. e. A
                /\
                <. ntpenv , <. ntpe2 , <. 0 , ntpn2 >. >. >. e. A
              )
              ->
              <. ntpenv , <. ( NTP4VCEsub e1 ntpe2 ) ,
                <. 0 , ( n1 - ntpn2 ) >. >. >. e. A
            )
      /\
      (
        A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
          A. e1 e. NTP4VCExpr A. ntpe2 e. NTP4VCExpr
            (
              <. ntpenv , <. e1 , <. 1 , 0 >. >. >. e. A
              ->
              <. ntpenv , <. ( NTP4VCEsub e1 ntpe2 ) ,
                <. 1 , 0 >. >. >. e. A
            )
        /\
        A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
          A. e1 e. NTP4VCExpr A. ntpe2 e. NTP4VCExpr A. n1 e. ZZ
            (
              (
                <. ntpenv , <. e1 , <. 0 , n1 >. >. >. e. A
                /\
                <. ntpenv , <. ntpe2 , <. 1 , 0 >. >. >. e. A
              )
              ->
              <. ntpenv , <. ( NTP4VCEsub e1 ntpe2 ) ,
                <. 1 , 0 >. >. >. e. A
            )
      )
    )
  ) $.
$}
ntp4vc-eval-graph-definition $a |- NTP4VCEvalGraph =
  |^| { x | ( NTP4VCEvalClosed x ) } $.
ntp4vc-eval-definition $a |- (
  NTP4VCEval A B C
) <-> (
  <. A , <. B , C >. >. e. NTP4VCEvalGraph
) $.

${
  $d x A B C $.
  ntp4vc-env-update-definition $a |- (
    NTP4VCEnvUpdate A B C
  ) = (
    x e. NTP4VCPVar |->
      if ( x = B , ( NTP4VCSome C ) , ( A ` x ) )
  ) $.
$}

${
  $d s v x $.
  ntp4vc-state-definition $a |- NTP4VCState =
    { s e.
      (
        NTP4VCModel
        X.
        (
          NTP4VCConstraint
          X.
          (
            ( ZZ ^m NTP4VCSVar )
            X.
            NTP4VCSVarSet
          )
        )
      )
      |
      (
        ( NTP4VCConstraintVars ` ( 1st ` ( 2nd ` s ) ) )
          C_
        ( NTP4VCToFSet ` ( 2nd ` ( 2nd ` ( 2nd ` s ) ) ) )
        /\
        A. x e. NTP4VCPVar A. v e. NTP4VCSVar
          (
            ( NTP4VCGet ` <. ( 1st ` s ) , x >. )
            =
            ( NTP4VCSome v )
            ->
            v e.
              ( NTP4VCToFSet ` ( 2nd ` ( 2nd ` ( 2nd ` s ) ) ) )
          )
      )
    } $.
$}
ntp4vc-sigma-definition $a |- NTP4VCSigma =
  ( s e. NTP4VCState |-> ( 1st ` s ) ) $.
ntp4vc-constr-definition $a |- NTP4VCConstrOf =
  ( s e. NTP4VCState |-> ( 1st ` ( 2nd ` s ) ) ) $.
ntp4vc-rho-definition $a |- NTP4VCRho =
  ( s e. NTP4VCState |->
    ( 1st ` ( 2nd ` ( 2nd ` s ) ) ) ) $.
ntp4vc-vars-definition $a |- NTP4VCVarsOf =
  ( s e. NTP4VCState |->
    ( NTP4VCToFSet ` ( 2nd ` ( 2nd ` ( 2nd ` s ) ) ) ) ) $.

ntp4vc-in-cmd-definition $a |- (
  NTP4VCInCmd A B C D E F
) <-> (
  <. 0 , <. <. <. <. B , C >. , D >. , E >. , F >. >. e. A
) $.
ntp4vc-in-while-definition $a |- (
  NTP4VCInWhile A B C D E F G H
) <-> (
  <. 1 ,
    <. <. <. <. <. <. B , C >. , D >. , E >. , F >. , G >. , H >.
  >. e. A
) $.
ntp4vc-permit-definition $a |- (
  NTP4VCPermit A B
) <-> (
  (
    ( 1st ` A ) = 0
    \/
    (
      ( 1st ` A ) = 1
      /\
      B < ( 2nd ` A )
    )
  )
) $.
ntp4vc-overflow-definition $a |- (
  NTP4VCOverflow A B
) <-> (
  (
    ( 1st ` A ) = 1
    /\
    ( 2nd ` A ) <_ B
  )
) $.

${
  $d b c ntpc1 ntpc2 ntpcnf ntpctr e ntpenv ntpenv1 ntpenv2 ntpenv3 n v A $.
  ntp4vc-exec-closed-definition $a |- (
    NTP4VCExecClosed A
  ) <-> (
    (
      (
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            ( NTP4VCInCmd
              A ntpcnf ntpenv NTP4VCCskip ntpenv 0 )
        /\
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. v e. NTP4VCPVar A. e e. NTP4VCExpr A. n e. ZZ
              (
                ( NTP4VCEval ntpenv e <. 0 , n >. )
                ->
                (
                  NTP4VCInCmd A ntpcnf ntpenv
                    ( NTP4VCCassign v e )
                    ( NTP4VCEnvUpdate ntpenv v n ) 0
                )
              )
      )
      /\
      (
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. v e. NTP4VCPVar A. e e. NTP4VCExpr
              (
                ( NTP4VCEval ntpenv e <. 1 , 0 >. )
                ->
                (
                  NTP4VCInCmd A ntpcnf ntpenv
                    ( NTP4VCCassign v e ) ntpenv 1
                )
              )
        /\
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv1 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. ntpenv2 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. ntpenv3 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
                A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd A. b e. 3
                  (
                    (
                      ( NTP4VCInCmd A ntpcnf ntpenv1 ntpc1 ntpenv2 0 )
                      /\
                      ( NTP4VCInCmd A ntpcnf ntpenv2 ntpc2 ntpenv3 b )
                    )
                    ->
                    (
                      NTP4VCInCmd A ntpcnf ntpenv1
                        ( NTP4VCCseq ntpc1 ntpc2 ) ntpenv3 b
                    )
                  )
      )
    )
    /\
    (
      (
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv1 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. ntpenv2 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd A. b e. 3
                (
                  (
                    ( NTP4VCInCmd A ntpcnf ntpenv1 ntpc1 ntpenv2 b )
                    /\
                    b =/= 0
                  )
                  ->
                  (
                    NTP4VCInCmd A ntpcnf ntpenv1
                      ( NTP4VCCseq ntpc1 ntpc2 ) ntpenv2 b
                  )
                )
        /\
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. ntpenv2 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. e e. NTP4VCExpr
                A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd A. b e. 3
                  (
                    (
                      ( NTP4VCEval ntpenv e <. 0 , 0 >. )
                      /\
                      ( NTP4VCInCmd A ntpcnf ntpenv ntpc2 ntpenv2 b )
                    )
                    ->
                    (
                      NTP4VCInCmd A ntpcnf ntpenv
                        ( NTP4VCCif e ntpc1 ntpc2 ) ntpenv2 b
                    )
                  )
      )
      /\
      (
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. ntpenv2 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. e e. NTP4VCExpr
                A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd
                  A. n e. ZZ A. b e. 3
                    (
                      (
                        (
                          n =/= 0
                          /\
                          ( NTP4VCEval ntpenv e <. 0 , n >. )
                        )
                        /\
                        ( NTP4VCInCmd A ntpcnf ntpenv ntpc1 ntpenv2 b )
                      )
                      ->
                      (
                        NTP4VCInCmd A ntpcnf ntpenv
                          ( NTP4VCCif e ntpc1 ntpc2 ) ntpenv2 b
                      )
                    )
        /\
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. e e. NTP4VCExpr A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd
              (
                ( NTP4VCEval ntpenv e <. 1 , 0 >. )
                ->
                (
                  NTP4VCInCmd A ntpcnf ntpenv
                    ( NTP4VCCif e ntpc1 ntpc2 ) ntpenv 1
                )
              )
      )
    )
    /\
    (
      (
        A. ntpcnf e. NTP4VCConfig
          A. ntpenv1 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. ntpenv2 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. e e. NTP4VCExpr A. c e. NTP4VCCmd A. b e. 3
                (
                  ( NTP4VCInWhile A ntpcnf 0 ntpenv1 e c ntpenv2 b )
                  ->
                  (
                    NTP4VCInCmd A ntpcnf ntpenv1
                      ( NTP4VCCwhile e c ) ntpenv2 b
                  )
                )
        /\
        A. ntpcnf e. NTP4VCConfig A. ntpctr e. ZZ
          A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
            A. e e. NTP4VCExpr A. c e. NTP4VCCmd
              (
                ( NTP4VCOverflow ntpcnf ntpctr )
                ->
                ( NTP4VCInWhile A ntpcnf ntpctr ntpenv e c ntpenv 2 )
              )
      )
      /\
      (
        (
          A. ntpcnf e. NTP4VCConfig A. ntpctr e. ZZ
            A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. e e. NTP4VCExpr A. c e. NTP4VCCmd
                (
                  (
                    ( NTP4VCPermit ntpcnf ntpctr )
                    /\
                    ( NTP4VCEval ntpenv e <. 0 , 0 >. )
                  )
                  ->
                  ( NTP4VCInWhile A ntpcnf ntpctr ntpenv e c ntpenv 0 )
                )
          /\
          A. ntpcnf e. NTP4VCConfig A. ntpctr e. ZZ
            A. ntpenv e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. e e. NTP4VCExpr A. c e. NTP4VCCmd
                (
                  (
                    ( NTP4VCPermit ntpcnf ntpctr )
                    /\
                    ( NTP4VCEval ntpenv e <. 1 , 0 >. )
                  )
                  ->
                  ( NTP4VCInWhile A ntpcnf ntpctr ntpenv e c ntpenv 1 )
                )
        )
        /\
        (
          A. ntpcnf e. NTP4VCConfig A. ntpctr e. ZZ
            A. ntpenv1 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. ntpenv2 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
                A. e e. NTP4VCExpr A. c e. NTP4VCCmd
                  A. n e. ZZ A. b e. 3
                    (
                      (
                        (
                          (
                            ( NTP4VCPermit ntpcnf ntpctr )
                            /\
                            ( NTP4VCEval ntpenv1 e <. 0 , n >. )
                          )
                          /\
                          n =/= 0
                        )
                        /\
                        (
                          ( NTP4VCInCmd A ntpcnf ntpenv1 c ntpenv2 b )
                          /\
                          b =/= 0
                        )
                      )
                      ->
                      ( NTP4VCInWhile A ntpcnf ntpctr ntpenv1 e c ntpenv2 b )
                    )
          /\
          A. ntpcnf e. NTP4VCConfig A. ntpctr e. ZZ
            A. ntpenv1 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
              A. ntpenv2 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
                A. ntpenv3 e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
                  A. e e. NTP4VCExpr A. c e. NTP4VCCmd
                    A. n e. ZZ A. b e. 3
                      (
                        (
                          (
                            (
                              ( NTP4VCPermit ntpcnf ntpctr )
                              /\
                              ( NTP4VCEval ntpenv1 e <. 0 , n >. )
                            )
                            /\
                            n =/= 0
                          )
                          /\
                          (
                            ( NTP4VCInCmd A ntpcnf ntpenv1 c ntpenv2 0 )
                            /\
                            (
                              NTP4VCInWhile A ntpcnf ( ntpctr + 1 )
                                ntpenv2 e c ntpenv3 b
                            )
                          )
                        )
                        ->
                        ( NTP4VCInWhile A ntpcnf ntpctr ntpenv1 e c ntpenv3 b )
                      )
        )
      )
    )
  ) $.
$}

ntp4vc-exec-graph-definition $a |- NTP4VCExecGraph =
  |^| { x | ( NTP4VCExecClosed x ) } $.
ntp4vc-exec-cmd-graph-definition $a |- NTP4VCExecCmdGraph =
  { q | <. 0 , q >. e. NTP4VCExecGraph } $.
ntp4vc-exec-while-graph-definition $a |- NTP4VCExecWhileGraph =
  { q | <. 1 , q >. e. NTP4VCExecGraph } $.

${
  $d s t A B J $.
  ntp4vc-pearl-imp-symbolic-interpreter-symbolic-interp-cmd-list-vc
    $a |- A. J e. ZZ
      A. A e. Word NTP4VCState A. B e. NTP4VCCmd
        (
          0 <_ J
          ->
          (
            A = (/)
            \/
            E. s e. NTP4VCState E. t e. Word NTP4VCState
              (
                A = ( <" s "> ++ t )
                /\
                (
                  NTP4VCStep
                    A s t J B
                    NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet
                    NTP4VCSolutionGraph NTP4VCConstrOf
                    NTP4VCExecCmdGraph NTP4VCMkLoop
                    NTP4VCState NTP4VCVarsOf
                )
              )
          )
        ) $.
$}
