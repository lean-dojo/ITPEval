$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_whileqtvc: the symbolic
  interpreter's verification condition for one while-loop step, including
  symbolic guard evaluation, nonzero and zero branch states, recursive body
  interpretation, termination measures, result construction, state extension,
  and forward/backward correspondence with concrete while execution. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The source development's shared IMP syntax, symbolic-state theory,
  evaluation relations, and command/while execution relations are inlined
  below. Keeping that context in this database makes the statement
  independently checkable without importing the sibling verification
  condition as an extra axiom.
$)

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
$c
  NTP4VCOption NTP4VCSome NTP4VCFiniteSubsets NTP4VCCompose
  NTP4VCStateExtends NTP4VCResultsExtend NTP4VCSolution
  NTP4VCExecWhile NTP4VCOutMember NTP4VCWhileForward
  NTP4VCWhileBackward NTP4VCWhileBundle
  NTP4VCPVar NTP4VCSVar NTP4VCModel NTP4VCSVarSet
  NTP4VCModelEmpty NTP4VCModelSet NTP4VCSVarSetMk NTP4VCToFSet
  NTP4VCConstraint NTP4VCExpr
  NTP4VCCmd NTP4VCConfig NTP4VCState NTP4VCRho NTP4VCSigma
  NTP4VCConstrOf NTP4VCVarsOf NTP4VCGet NTP4VCSolutionGraph
  NTP4VCExecWhileGraph NTP4VCMkLoop NTP4VCConstraintVars
  NTP4VCLoopLimit
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
  NTP4VCExecCmdGraph NTP4VCInCmd NTP4VCInWhile
  NTP4VCPermit NTP4VCOverflow
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
ntp4vc-exec-while-syntax
  $a wff ( NTP4VCExecWhile A B C D E F G H ) $.
ntp4vc-out-member-syntax
  $a wff ( NTP4VCOutMember A B C D E ) $.
ntp4vc-while-forward-syntax
  $a wff (
    NTP4VCWhileForward A B C D E F G H I J K L M N O P Q
  ) $.
ntp4vc-while-backward-syntax
  $a wff (
    NTP4VCWhileBackward A B C D E F G H I J K L M N O P Q
  ) $.
ntp4vc-while-bundle-syntax
  $a wff (
    NTP4VCWhileBundle A B C D E F G H I J K L M N O P Q R
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

ntp4vc-exec-while-definition $a |- (
  NTP4VCExecWhile A B C D E F G H
) <-> (
  <. <. <. <. <. <. B , C >. , D >. , E >. , F >. , G >. , H >. e. A
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
  $d b g s A B C D E F G H I J K L M N O P Q $.

  $(
    A is the input state; B, C, D are the normal, unbound-variable, and
    loop-limit result sets. E, F, G, and H are n, ctr, the loop expression,
    and the loop command. I through Q are the program-variable carrier, rho,
    sigma, get, is_solution, constr, exec_while, mk_loop_cnf, and the
    symbolic-state carrier.
  $)
  ntp4vc-while-forward-definition $a |- (
    NTP4VCWhileForward A B C D E F G H I J K L M N O P Q
  ) <-> (
    A. g e. ( ( NTP4VCOption ZZ ) ^m I )
      A. b e. { 0 , 1 , 2 }
        (
          (
            NTP4VCExecWhile
              O
              ( P ` E )
              F
              ( NTP4VCCompose I J K L A )
              G H g b
          )
          ->
          E. s e. Q
            (
              ( NTP4VCOutMember b s B C D )
              /\
              (
                ( NTP4VCSolution M J N s )
                /\
                g = ( NTP4VCCompose I J K L s )
              )
            )
        )
  ) $.
$}

${
  $d b s A B C D E F G H I J K L M N O P Q $.

  ntp4vc-while-backward-definition $a |- (
    NTP4VCWhileBackward A B C D E F G H I J K L M N O P Q
  ) <-> (
    A. b e. { 0 , 1 , 2 } A. s e. Q
      (
        ( NTP4VCOutMember b s B C D )
        ->
        (
          ( NTP4VCSolution M J N s )
          ->
          (
            ( NTP4VCSolution M J N A )
            /\
            (
              NTP4VCExecWhile
                O
                ( P ` E )
                F
                ( NTP4VCCompose I J K L A )
                G H
                ( NTP4VCCompose I J K L s )
                b
            )
          )
        )
      )
  ) $.
$}

ntp4vc-while-bundle-definition $a |- (
  NTP4VCWhileBundle A B C D E F G H I J K L M N O P Q R
) <-> (
  ( NTP4VCResultsExtend A B C D R J )
  /\
  (
    (
      ( NTP4VCSolution M J N A )
      ->
      (
        NTP4VCWhileForward
          A B C D E F G H I J K L M N O P Q
      )
    )
    /\
    (
      NTP4VCWhileBackward
        A B C D E F G H I J K L M N O P Q
    )
  )
) $.
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
                A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd
                  A. b e. { 0 , 1 , 2 }
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
              A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd
                A. b e. { 0 , 1 , 2 }
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
                A. ntpc1 e. NTP4VCCmd A. ntpc2 e. NTP4VCCmd
                  A. b e. { 0 , 1 , 2 }
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
                  A. n e. ZZ A. b e. { 0 , 1 , 2 }
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
              A. e e. NTP4VCExpr A. c e. NTP4VCCmd
                A. b e. { 0 , 1 , 2 }
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
                  A. n e. ZZ A. b e. { 0 , 1 , 2 }
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
                    A. n e. ZZ A. b e. { 0 , 1 , 2 }
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

$(
  The inlined shared theory is the accepted exact SetMM encoding of this
  development's typed IMP syntax, symbolic syntax, constraints, environments,
  symbolic states, solution predicate, and mutually inductive command/while
  execution relations.

  Unlike the sibling list VC, this statement observes SymStateSet values
  through both to_fset and to_list. NTP4VCStateSet is therefore retained as an
  opaque inhabited carrier, with fixed to_fset, to_list, and of_list maps and
  their source membership specifications. NTP4VCVarsRaw projects the original
  opaque Svar.set component of a symbolic state, so branch-state equality does
  not collapse typed structure to its finite-set observation.

  The named predicates below are only definitional abbreviations of source
  subformulas. Finite-set cardinality equations that accompany exact
  finite-set equalities in the source are omitted because the equalities imply
  them bidirectionally. All source quantifiers retain their full integer,
  function, word, finite-set, wrapper, expression, command, and state domains.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCVarsRaw NTP4VCStateSet NTP4VCStateSetToFSet
  NTP4VCStateSetToList NTP4VCStateSetOfList
  NTP4VCSymOK NTP4VCStateValid NTP4VCBranchState
  NTP4VCNoSolution NTP4VCEmptyResults NTP4VCExecCmd
  NTP4VCCmdForward NTP4VCCmdBackward NTP4VCCmdBundle
  NTP4VCListConclusion NTP4VCRecursiveCase
  NTP4VCGuardedBody NTP4VCGuardedExit NTP4VCNormalConstruction
  NTP4VCResultPremise NTP4VCObligation NTP4VCFinalConclusion
$.

ntp4vc-vars-raw-syntax $a class NTP4VCVarsRaw $.
ntp4vc-state-set-syntax $a class NTP4VCStateSet $.
ntp4vc-state-set-to-fset-syntax $a class NTP4VCStateSetToFSet $.
ntp4vc-state-set-to-list-syntax $a class NTP4VCStateSetToList $.
ntp4vc-state-set-of-list-syntax $a class NTP4VCStateSetOfList $.

ntp4vc-sym-ok-syntax
  $a wff ( NTP4VCSymOK A B C ) $.
ntp4vc-state-valid-syntax
  $a wff ( NTP4VCStateValid A B C ) $.
ntp4vc-branch-state-syntax
  $a wff ( NTP4VCBranchState A B C D ) $.
ntp4vc-no-solution-syntax
  $a wff ( NTP4VCNoSolution A ) $.
ntp4vc-empty-results-syntax
  $a wff ( NTP4VCEmptyResults A B C ) $.
ntp4vc-exec-cmd-syntax
  $a wff ( NTP4VCExecCmd A B C D E ) $.
ntp4vc-cmd-forward-syntax
  $a wff ( NTP4VCCmdForward A B C D E F ) $.
ntp4vc-cmd-backward-syntax
  $a wff ( NTP4VCCmdBackward A B C D E F ) $.
ntp4vc-cmd-bundle-syntax
  $a wff ( NTP4VCCmdBundle A B C D E F ) $.
ntp4vc-list-conclusion-syntax
  $a wff ( NTP4VCListConclusion A B C D E F G H ) $.
ntp4vc-recursive-case-syntax
  $a wff ( NTP4VCRecursiveCase A B C D E F G H ) $.
ntp4vc-guarded-body-syntax
  $a wff ( NTP4VCGuardedBody A B C D E F G H ) $.
ntp4vc-guarded-exit-syntax
  $a wff ( NTP4VCGuardedExit A B C D ) $.
ntp4vc-normal-construction-syntax
  $a wff ( NTP4VCNormalConstruction A B C D E F G H ) $.
ntp4vc-result-premise-syntax
  $a wff ( NTP4VCResultPremise A B C D E F G H ) $.
ntp4vc-obligation-syntax
  $a wff ( NTP4VCObligation A B C D E ) $.
ntp4vc-final-conclusion-syntax
  $a wff ( NTP4VCFinalConclusion A B C D E F G H ) $.

ntp4vc-vars-raw-definition $a |- NTP4VCVarsRaw =
  ( s e. NTP4VCState |->
    ( 2nd ` ( 2nd ` ( 2nd ` s ) ) ) ) $.

ntp4vc-state-set-set $a |- NTP4VCStateSet e. _V $.
ntp4vc-state-set-inhabited $a |- NTP4VCStateSet =/= (/) $.
ntp4vc-state-set-to-fset-type $a |-
  NTP4VCStateSetToFSet e.
    ( ( NTP4VCFiniteSubsets NTP4VCState ) ^m NTP4VCStateSet ) $.
ntp4vc-state-set-to-list-type $a |-
  NTP4VCStateSetToList e.
    ( ( Word NTP4VCState ) ^m NTP4VCStateSet ) $.
ntp4vc-state-set-of-list-type $a |-
  NTP4VCStateSetOfList e.
    ( NTP4VCStateSet ^m ( Word NTP4VCState ) ) $.

${
  $d q s $.
  ntp4vc-state-set-to-list-spec $a |-
    A. q e. NTP4VCStateSet A. s e. NTP4VCState
      (
        s e. ( NTP4VCStateSetToFSet ` q )
        <->
        s e. ran ( NTP4VCStateSetToList ` q )
      ) $.
$}

${
  $d s w $.
  ntp4vc-state-set-of-list-spec $a |-
    A. w e. Word NTP4VCState A. s e. NTP4VCState
      (
        s e. ( NTP4VCStateSetToFSet ` ( NTP4VCStateSetOfList ` w ) )
        <->
        s e. ran w
      ) $.
$}

${
  $d v x z A B C $.
  ntp4vc-sym-ok-definition $a |- (
    NTP4VCSymOK A B C
  ) <-> (
    E. z e. ZZ
      (
        <. ( NTP4VCRho ` A ) , <. C , z >. >. e. NTP4VCSEvalGraph
        /\
        (
          ( NTP4VCEval
            ( NTP4VCCompose
              NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet A )
            B
            <. 0 , z >.
          )
          /\
          A. v e. NTP4VCSVar
            (
              <. C , v >. e. NTP4VCSExprVarsGraph
              ->
              E. x e. NTP4VCPVar
                (
                  ( NTP4VCGet ` <. ( NTP4VCSigma ` A ) , x >. )
                  =
                  ( NTP4VCSome v )
                )
            )
        )
      )
  ) $.
$}

${
  $d v x A B C $.
  ntp4vc-state-valid-definition $a |- (
    NTP4VCStateValid A B C
  ) <-> (
    ( NTP4VCConstraintVars ` B ) C_ C
    /\
    A. x e. NTP4VCPVar A. v e. NTP4VCSVar
      (
        ( NTP4VCGet ` <. A , x >. ) = ( NTP4VCSome v )
        ->
        v e. C
      )
  ) $.
$}

ntp4vc-branch-state-definition $a |- (
  NTP4VCBranchState A B C D
) <-> (
  ( NTP4VCSigma ` A ) = ( NTP4VCSigma ` B )
  /\
  (
    ( NTP4VCConstrOf ` A )
    =
    if (
      D = 1 ,
      ( NTP4VCCconj
        ( NTP4VCConstrOf ` B )
        ( NTP4VCCneq C ( NTP4VCSLit 0 ) )
      ) ,
      ( NTP4VCCconj
        ( NTP4VCConstrOf ` B )
        ( NTP4VCCeq C ( NTP4VCSLit 0 ) )
      )
    )
  )
  /\
  (
    ( NTP4VCRho ` A ) = ( NTP4VCRho ` B )
    /\
    ( NTP4VCVarsRaw ` A ) = ( NTP4VCVarsRaw ` B )
  )
) $.

${
  $d r A $.
  ntp4vc-no-solution-definition $a |- (
    NTP4VCNoSolution A
  ) <-> (
    A. r e. ( ZZ ^m NTP4VCSVar )
      -. <. r , ( NTP4VCConstrOf ` A ) >. e. NTP4VCSolutionGraph
  ) $.
$}

ntp4vc-empty-results-definition $a |- (
  NTP4VCEmptyResults A B C
) <-> (
  ( NTP4VCStateSetToFSet ` A ) = (/)
  /\
  (
    ( NTP4VCStateSetToFSet ` B ) = (/)
    /\
    ( NTP4VCStateSetToFSet ` C ) = (/)
  )
) $.

ntp4vc-exec-cmd-definition $a |- (
  NTP4VCExecCmd A B C D E
) <-> (
  <. <. <. <. A , B >. , C >. , D >. , E >. e. NTP4VCExecCmdGraph
) $.

${
  $d b g s A B C D E F $.
  ntp4vc-cmd-forward-definition $a |- (
    NTP4VCCmdForward A B C D E F
  ) <-> (
    A. g e. ( ( NTP4VCOption ZZ ) ^m NTP4VCPVar )
      A. b e. { 0 , 1 , 2 }
        (
          (
            NTP4VCExecCmd
              ( NTP4VCMkLoop ` E )
              ( NTP4VCCompose
                NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet A )
              F g b
          )
          ->
          E. s e. NTP4VCState
            (
              (
                NTP4VCOutMember b s
                  ( NTP4VCStateSetToFSet ` B )
                  ( NTP4VCStateSetToFSet ` C )
                  ( NTP4VCStateSetToFSet ` D )
              )
              /\
              (
                ( NTP4VCSolution
                  NTP4VCSolutionGraph NTP4VCRho NTP4VCConstrOf s )
                /\
                g =
                  ( NTP4VCCompose
                    NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet s )
              )
            )
        )
  ) $.
$}

${
  $d b s A B C D E F $.
  ntp4vc-cmd-backward-definition $a |- (
    NTP4VCCmdBackward A B C D E F
  ) <-> (
    A. b e. { 0 , 1 , 2 } A. s e. NTP4VCState
      (
        (
          NTP4VCOutMember b s
            ( NTP4VCStateSetToFSet ` B )
            ( NTP4VCStateSetToFSet ` C )
            ( NTP4VCStateSetToFSet ` D )
        )
        ->
        (
          ( NTP4VCSolution
            NTP4VCSolutionGraph NTP4VCRho NTP4VCConstrOf s )
          ->
          (
            ( NTP4VCSolution
              NTP4VCSolutionGraph NTP4VCRho NTP4VCConstrOf A )
            /\
            (
              NTP4VCExecCmd
                ( NTP4VCMkLoop ` E )
                ( NTP4VCCompose
                  NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet A )
                F
                ( NTP4VCCompose
                  NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet s )
                b
            )
          )
        )
      )
  ) $.
$}

ntp4vc-cmd-bundle-definition $a |- (
  NTP4VCCmdBundle A B C D E F
) <-> (
  (
    NTP4VCResultsExtend A
      ( NTP4VCStateSetToFSet ` B )
      ( NTP4VCStateSetToFSet ` C )
      ( NTP4VCStateSetToFSet ` D )
      NTP4VCVarsOf NTP4VCRho
  )
  /\
  (
    (
      ( NTP4VCSolution
        NTP4VCSolutionGraph NTP4VCRho NTP4VCConstrOf A )
      ->
      ( NTP4VCCmdForward A B C D E F )
    )
    /\
    ( NTP4VCCmdBackward A B C D E F )
  )
) $.

${
  $d b g s t A B C D E F G H $.
  ntp4vc-list-conclusion-definition $a |- (
    NTP4VCListConclusion A B C D E F G H
  ) <-> (
    A. s e.
      (
        ( NTP4VCStateSetToFSet ` B )
        u.
        (
          ( NTP4VCStateSetToFSet ` C )
          u.
          ( NTP4VCStateSetToFSet ` D )
        )
      )
      E. t e.
        ( NTP4VCStateSetToFSet ` ( NTP4VCStateSetOfList ` A ) )
        ( NTP4VCStateExtends t s NTP4VCVarsOf NTP4VCRho )
    /\
    (
      A. t e.
        ( NTP4VCStateSetToFSet ` ( NTP4VCStateSetOfList ` A ) )
        (
          ( NTP4VCSolution
            NTP4VCSolutionGraph NTP4VCRho NTP4VCConstrOf t )
          ->
          (
            NTP4VCWhileForward
              t
              ( NTP4VCStateSetToFSet ` B )
              ( NTP4VCStateSetToFSet ` C )
              ( NTP4VCStateSetToFSet ` D )
              E F G H NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet
              NTP4VCSolutionGraph NTP4VCConstrOf NTP4VCExecWhileGraph
              NTP4VCMkLoop NTP4VCState
          )
        )
      /\
      A. b e. { 0 , 1 , 2 } A. s e. NTP4VCState
        (
          (
            NTP4VCOutMember b s
              ( NTP4VCStateSetToFSet ` B )
              ( NTP4VCStateSetToFSet ` C )
              ( NTP4VCStateSetToFSet ` D )
          )
          ->
          (
            ( NTP4VCSolution
              NTP4VCSolutionGraph NTP4VCRho NTP4VCConstrOf s )
            ->
            E. t e.
              ( NTP4VCStateSetToFSet ` ( NTP4VCStateSetOfList ` A ) )
              (
                ( NTP4VCSolution
                  NTP4VCSolutionGraph NTP4VCRho NTP4VCConstrOf t )
                /\
                (
                  NTP4VCExecWhile
                    NTP4VCExecWhileGraph
                    ( NTP4VCMkLoop ` E )
                    F
                    ( NTP4VCCompose
                      NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet t )
                    G H
                    ( NTP4VCCompose
                      NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet s )
                    b
                )
              )
          )
        )
    )
  ) $.
$}

${
  $d s A B C D E F G H $.
  ntp4vc-recursive-case-definition $a |- (
    NTP4VCRecursiveCase A B C D E F G H
  ) <-> (
    E. s e. NTP4VCStateSet
      E. t e. NTP4VCStateSet
        E. x e. NTP4VCStateSet
          (
            ( NTP4VCCmdBundle A s t x E H )
            /\
            (
              (
                A. q e. NTP4VCState
                  (
                    q e. ( NTP4VCStateSetToFSet ` s )
                    <->
                    q e. ran ( NTP4VCStateSetToList ` s )
                  )
              )
              /\
              E. y e. NTP4VCStateSet E. z e. NTP4VCStateSet
                (
                  (
                    NTP4VCListConclusion
                      ( NTP4VCStateSetToList ` s )
                      B y z E ( F + 1 ) G H
                  )
                  /\
                  (
                    ( NTP4VCStateSetToFSet ` D )
                    =
                    (
                      ( NTP4VCStateSetToFSet ` x )
                      u.
                      ( NTP4VCStateSetToFSet ` z )
                    )
                    /\
                    ( NTP4VCStateSetToFSet ` C )
                    =
                    (
                      ( NTP4VCStateSetToFSet ` t )
                      u.
                      ( NTP4VCStateSetToFSet ` y )
                    )
                  )
                )
            )
          )
  ) $.
$}

${
  $d t A B C D E F G H $.
  ntp4vc-guarded-body-definition $a |- (
    NTP4VCGuardedBody A B C D E F G H
  ) <-> (
    E. t e. { 0 , 1 }
      (
        ( t = 0 -> ( NTP4VCNoSolution A ) )
        /\
        if (
          t = 1 ,
          ( NTP4VCRecursiveCase A B C D E F G H ) ,
          ( NTP4VCEmptyResults B C D )
        )
      )
  ) $.
$}

${
  $d t A B C D $.
  ntp4vc-guarded-exit-definition $a |- (
    NTP4VCGuardedExit A B C D
  ) <-> (
    E. t e. { 0 , 1 }
      (
        ( t = 0 -> ( NTP4VCNoSolution A ) )
        /\
        if (
          t = 1 ,
          (
            ( NTP4VCStateSetToFSet ` D ) = (/)
            /\
            (
              ( NTP4VCStateSetToFSet ` C ) = (/)
              /\
              ( NTP4VCStateSetToFSet ` B ) = { A }
            )
          ) ,
          ( NTP4VCEmptyResults B C D )
        )
      )
  ) $.
$}

${
  $d s t x y z A B C D E F G H $.
  ntp4vc-normal-construction-definition $a |- (
    NTP4VCNormalConstruction A B C D E F G H
  ) <-> (
    E. x e. NTP4VCSExpr
      (
        ( NTP4VCSymOK A G x )
        /\
        E. s e. NTP4VCState
          (
            ( NTP4VCBranchState s A x 1 )
            /\
            E. t e. NTP4VCState
              (
                ( NTP4VCBranchState t A x 0 )
                /\
                E. y e. NTP4VCStateSet
                  E. z e. NTP4VCStateSet
                    E. q e. NTP4VCStateSet
                      (
                        ( NTP4VCGuardedBody s y z q E F G H )
                        /\
                        E. u e. NTP4VCStateSet
                          E. v e. NTP4VCStateSet
                            E. w e. NTP4VCStateSet
                              (
                                ( NTP4VCGuardedExit t u v w )
                                /\
                                (
                                  ( NTP4VCStateSetToFSet ` B )
                                  =
                                  (
                                    ( NTP4VCStateSetToFSet ` y )
                                    u.
                                    ( NTP4VCStateSetToFSet ` u )
                                  )
                                  /\
                                  (
                                    ( NTP4VCStateSetToFSet ` C )
                                    =
                                    (
                                      ( NTP4VCStateSetToFSet ` z )
                                      u.
                                      ( NTP4VCStateSetToFSet ` v )
                                    )
                                    /\
                                    ( NTP4VCStateSetToFSet ` D )
                                    =
                                    (
                                      ( NTP4VCStateSetToFSet ` q )
                                      u.
                                      ( NTP4VCStateSetToFSet ` w )
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

ntp4vc-result-premise-definition $a |- (
  NTP4VCResultPremise A B C D E F G H
) <-> (
  if (
    F = E ,
    (
      ( NTP4VCStateSetToFSet ` D ) = { A }
      /\
      (
        ( NTP4VCStateSetToFSet ` C ) = (/)
        /\
        ( NTP4VCStateSetToFSet ` B ) = (/)
      )
    ) ,
    (
      ( NTP4VCNormalConstruction A B C D E F G H )
      \/
      (
        ( NTP4VCEval
          ( NTP4VCCompose
            NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet A )
          G
          <. 1 , 0 >.
        )
        /\
        (
          ( NTP4VCStateSetToFSet ` D ) = (/)
          /\
          (
            ( NTP4VCStateSetToFSet ` B ) = (/)
            /\
            ( NTP4VCStateSetToFSet ` C ) = { A }
          )
        )
      )
    )
  )
) $.

${
  $d q s t x A B C D E $.
  ntp4vc-obligation-definition $a |- (
    NTP4VCObligation A B C D E
  ) <-> (
    (
      C =/= B
      ->
      A. x e. NTP4VCSExpr
        (
          ( NTP4VCSymOK A D x )
          ->
          (
            ( NTP4VCStateValid
              ( NTP4VCSigma ` A )
              ( NTP4VCCconj
                ( NTP4VCConstrOf ` A )
                ( NTP4VCCneq x ( NTP4VCSLit 0 ) )
              )
              ( NTP4VCVarsOf ` A )
            )
            /\
            A. s e. NTP4VCState
              (
                ( NTP4VCBranchState s A x 1 )
                ->
                (
                  ( NTP4VCStateValid
                    ( NTP4VCSigma ` A )
                    ( NTP4VCCconj
                      ( NTP4VCConstrOf ` A )
                      ( NTP4VCCeq x ( NTP4VCSLit 0 ) )
                    )
                    ( NTP4VCVarsOf ` A )
                  )
                  /\
                  A. t e. NTP4VCState
                    (
                      ( NTP4VCBranchState t A x 0 )
                      ->
                      (
                        ( 1 = 0 -> ( NTP4VCNoSolution s ) )
                        ->
                        (
                          0 <_ B
                          /\
                          A. q e. NTP4VCStateSet
                            A. y e. NTP4VCStateSet
                              A. z e. NTP4VCStateSet
                                (
                                  ( NTP4VCCmdBundle s q y z B E )
                                  ->
                                  (
                                    (
                                      A. v e. NTP4VCState
                                        (
                                          v e.
                                            ( NTP4VCStateSetToFSet ` q )
                                          <->
                                          v e. ran
                                            ( NTP4VCStateSetToList ` q )
                                        )
                                    )
                                    ->
                                    (
                                      (
                                        (
                                          0 <_ ( B - C )
                                          /\
                                          ( B - ( C + 1 ) ) < ( B - C )
                                        )
                                        \/
                                        (
                                          (
                                            ( B - C ) = ( B - ( C + 1 ) )
                                            /\
                                            0 <_ 0
                                          )
                                          /\
                                          (
                                            # `
                                            ( NTP4VCStateSetToList ` q )
                                          ) < 0
                                        )
                                      )
                                      /\
                                      (
                                        0 <_ ( C + 1 )
                                        /\
                                        ( C + 1 ) <_ B
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

ntp4vc-final-conclusion-definition $a |- (
  NTP4VCFinalConclusion A B C D E F G H
) <-> (
  NTP4VCWhileBundle
    A
    ( NTP4VCStateSetToFSet ` B )
    ( NTP4VCStateSetToFSet ` C )
    ( NTP4VCStateSetToFSet ` D )
    E F G H NTP4VCPVar NTP4VCRho NTP4VCSigma NTP4VCGet
    NTP4VCSolutionGraph NTP4VCConstrOf NTP4VCExecWhileGraph
    NTP4VCMkLoop NTP4VCState NTP4VCVarsOf
) $.

${
  $d a b c l m s t u $.
  ntp4vc-pearl-imp-symbolic-interpreter-symbolic-interp-while-vc
    $a |- A. l e. ZZ A. m e. ZZ
      A. a e. NTP4VCState
        A. b e. NTP4VCExpr A. c e. NTP4VCCmd
          (
            (
              0 <_ l
              /\
              l <_ m
            )
            ->
            (
              ( NTP4VCObligation a m l b c )
              /\
              A. s e. NTP4VCStateSet
                A. t e. NTP4VCStateSet
                  A. u e. NTP4VCStateSet
                    (
                      ( NTP4VCResultPremise a s t u m l b c )
                      ->
                      ( NTP4VCFinalConclusion a s t u m l b c )
                    )
            )
          ) $.
$}
