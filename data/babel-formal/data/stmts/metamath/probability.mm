$(
  Statement-only formalization of the Babel-formal topic probability. This file contains no
  proof.
$)

$(
  Statement-only encoding of ring-valued probability on events over an
  arbitrary outcome sort, together with finite event lists, conditional
  probability, independence, disjoint finite unions, and inclusion-exclusion.

  Scalar, point, event, and list quantifiers use dedicated binder-variable
  sorts, so compound terms cannot occupy binder position.  Probability maps
  and conditional-probability maps are schematic variables.
  ProbContext contains the common probability laws used by the derived
  results; the two non-indexed source axioms are stated under that same
  probability context.
  All mathematical declarations and translated results are unproved $a
  assertions.  This database contains no proof statements.
$)

$c
  svar pvar evar elvar slvar
  scalar point event eventlist scalarlist probmap cprobmap wff |-
  ( )
  zero one neg add mul
  empty whole inter union compl diff
  nilE consE inE pairwise bigUnion
  nilR consR mapProb foldAdd
  prob cprob
  holds =R =E =EL =RL
  -> <-> /\ \/ -.
  T. F.
  A.r A.w A.e A.el A.rl
  disjoint indep Ring ProbContext
$.

$v
  x y z
  omega
  E F
  zs
  us
  r s t
  A B C D
  xs ys
  rs ss
  P Q
  ph ps
$.

bsx $f svar x $.
bsy $f svar y $.
bsz $f svar z $.

bpomega $f pvar omega $.

beE $f evar E $.
beF $f evar F $.

belzs $f elvar zs $.

bslus $f slvar us $.

scalar-r $f scalar r $.
scalar-s $f scalar s $.
scalar-t $f scalar t $.

eA $f event A $.
eB $f event B $.
eC $f event C $.
eD $f event D $.

elxs $f eventlist xs $.
elys $f eventlist ys $.

slrs $f scalarlist rs $.
slss $f scalarlist ss $.

pmP $f probmap P $.
cmQ $f cprobmap Q $.

wph $f wff ph $.
wps $f wff ps $.

scalar-var-term $a scalar x $.
point-var-term $a point omega $.
event-var-term $a event E $.
event-list-var-term $a eventlist zs $.
scalar-list-var-term $a scalarlist us $.

zero-term $a scalar zero $.
one-term $a scalar one $.
neg-term $a scalar ( neg r ) $.
add-term $a scalar ( add r s ) $.
mul-term $a scalar ( mul r s ) $.

empty-event $a event empty $.
whole-event $a event whole $.
inter-event $a event ( inter A B ) $.
union-event $a event ( union A B ) $.
compl-event $a event ( compl A ) $.
diff-event $a event ( diff A B ) $.

nil-event-list $a eventlist nilE $.
cons-event-list $a eventlist ( consE A xs ) $.

nil-scalar-list $a scalarlist nilR $.
cons-scalar-list $a scalarlist ( consR r rs ) $.

big-union-term $a event ( bigUnion xs ) $.
map-prob-term $a scalarlist ( mapProb P xs ) $.
fold-add-term $a scalar ( foldAdd rs ) $.

prob-term $a scalar ( prob P A ) $.
cprob-term $a scalar ( cprob Q A B ) $.

holds-formula $a wff ( holds A omega ) $.
scalar-eq-formula $a wff ( r =R s ) $.
event-eq-formula $a wff ( A =E B ) $.
event-list-eq-formula $a wff ( xs =EL ys ) $.
scalar-list-eq-formula $a wff ( rs =RL ss ) $.

imp-formula $a wff ( ph -> ps ) $.
iff-formula $a wff ( ph <-> ps ) $.
and-formula $a wff ( ph /\ ps ) $.
or-formula $a wff ( ph \/ ps ) $.
not-formula $a wff ( -. ph ) $.
true-formula $a wff T. $.
false-formula $a wff F. $.

excluded-middle $a |- ( ph \/ ( -. ph ) ) $.

forall-scalar-formula $a wff ( A.r x ph ) $.
forall-point-formula $a wff ( A.w omega ph ) $.
forall-event-formula $a wff ( A.e E ph ) $.
forall-event-list-formula $a wff ( A.el zs ph ) $.
forall-scalar-list-formula $a wff ( A.rl us ph ) $.

$d x y z $.
$d E F $.
$d E A $.
$d E xs $.

in-event-list-formula $a wff ( inE A xs ) $.
pairwise-formula $a wff ( pairwise xs ) $.
disjoint-formula $a wff ( disjoint A B ) $.
indep-formula $a wff ( indep P A B ) $.
ring-formula $a wff Ring $.
prob-context-formula $a wff ( ProbContext P Q ) $.

event-eq-def $a |- (
  ( A =E B )
  <->
  ( A.w omega
    ( ( holds A omega ) <-> ( holds B omega ) )
  )
) $.

empty-def $a |- (
  A.w omega
    ( ( holds empty omega ) <-> F. )
) $.

whole-def $a |- (
  A.w omega
    ( ( holds whole omega ) <-> T. )
) $.

inter-def $a |- (
  A.w omega
    (
      ( holds ( inter A B ) omega )
      <->
      ( ( holds A omega ) /\ ( holds B omega ) )
    )
) $.

union-def $a |- (
  A.w omega
    (
      ( holds ( union A B ) omega )
      <->
      ( ( holds A omega ) \/ ( holds B omega ) )
    )
) $.

compl-def $a |- (
  A.w omega
    (
      ( holds ( compl A ) omega )
      <->
      ( -. ( holds A omega ) )
    )
) $.

diff-def $a |- (
  A.w omega
    (
      ( holds ( diff A B ) omega )
      <->
      ( ( holds A omega ) /\ ( -. ( holds B omega ) ) )
    )
) $.

disjoint-def $a |- (
  ( disjoint A B )
  <->
  ( A.w omega
    ( -. ( holds ( inter A B ) omega ) )
  )
) $.

in-event-list-nil $a |- (
  ( inE A nilE ) <-> F.
) $.

in-event-list-cons $a |- (
  ( inE A ( consE B xs ) )
  <->
  ( ( A =E B ) \/ ( inE A xs ) )
) $.

pairwise-nil $a |- (
  ( pairwise nilE ) <-> T.
) $.

pairwise-cons $a |- (
  ( pairwise ( consE A xs ) )
  <->
  (
    ( A.e E
      ( ( inE E xs ) -> ( disjoint A E ) )
    )
    /\
    ( pairwise xs )
  )
) $.

big-union-nil $a |- (
  ( bigUnion nilE ) =E empty
) $.

big-union-cons $a |- (
  ( bigUnion ( consE A xs ) )
  =E
  ( union A ( bigUnion xs ) )
) $.

map-prob-nil $a |- (
  ( mapProb P nilE ) =RL nilR
) $.

map-prob-cons $a |- (
  ( mapProb P ( consE A xs ) )
  =RL
  ( consR ( prob P A ) ( mapProb P xs ) )
) $.

fold-add-nil $a |- (
  ( foldAdd nilR ) =R zero
) $.

fold-add-cons $a |- (
  ( foldAdd ( consR r rs ) )
  =R
  ( add r ( foldAdd rs ) )
) $.

indep-def $a |- (
  ( indep P A B )
  <->
  (
    ( prob P ( inter A B ) )
    =R
    ( mul ( prob P A ) ( prob P B ) )
  )
) $.

ring-def $a |- (
  Ring
  <->
  (
    ( -. ( one =R zero ) )
    /\
    (
      ( A.r x
        ( A.r y
          ( ( add x y ) =R ( add y x ) )
        )
      )
      /\
      (
        ( A.r x
          ( A.r y
            ( A.r z
              (
                ( add ( add x y ) z )
                =R
                ( add x ( add y z ) )
              )
            )
          )
        )
        /\
        (
          ( A.r x
            ( ( add x zero ) =R x )
          )
          /\
          (
            ( A.r x
              ( ( add x ( neg x ) ) =R zero )
            )
            /\
            (
              ( A.r x
                ( A.r y
                  ( ( mul x y ) =R ( mul y x ) )
                )
              )
              /\
              (
                ( A.r x
                  ( A.r y
                    ( A.r z
                      (
                        ( mul ( mul x y ) z )
                        =R
                        ( mul x ( mul y z ) )
                      )
                    )
                  )
                )
                /\
                (
                  ( A.r x
                    ( ( mul x one ) =R x )
                  )
                  /\
                  (
                    ( A.r x
                      ( A.r y
                        ( A.r z
                          (
                            ( mul x ( add y z ) )
                            =R
                            ( add ( mul x y ) ( mul x z ) )
                          )
                        )
                      )
                    )
                    /\
                    (
                      ( A.r x
                        ( ( mul x zero ) =R zero )
                      )
                      /\
                      (
                        ( A.r x
                          ( A.r y
                            (
                              ( ( mul x y ) =R zero )
                              ->
                              ( ( x =R zero ) \/ ( y =R zero ) )
                            )
                          )
                        )
                        /\
                        (
                          ( ( neg zero ) =R zero )
                          /\
                          (
                            ( A.r x
                              ( ( neg ( neg x ) ) =R x )
                            )
                            /\
                            (
                              ( A.r x
                                ( A.r y
                                  (
                                    ( mul x ( neg y ) )
                                    =R
                                    ( neg ( mul x y ) )
                                  )
                                )
                              )
                              /\
                              ( A.r x
                                ( A.r y
                                  (
                                    ( mul ( neg x ) y )
                                    =R
                                    ( neg ( mul x y ) )
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

prob-context-def $a |- (
  ( ProbContext P Q )
  <->
  (
    Ring
    /\
    (
      ( A.e E
        ( A.e F
          (
            ( E =E F )
            ->
            ( ( prob P E ) =R ( prob P F ) )
          )
        )
      )
      /\
      (
        ( ( prob P empty ) =R zero )
        /\
        (
          ( ( prob P whole ) =R one )
          /\
          (
            ( A.e E
              ( A.e F
                (
                  ( prob P ( union E F ) )
                  =R
                  (
                    add
                      ( prob P E )
                      (
                        add
                          ( prob P F )
                          ( neg ( prob P ( inter E F ) ) )
                      )
                  )
                )
              )
            )
            /\
            (
              ( A.e E
                (
                  ( prob P ( compl E ) )
                  =R
                  ( add one ( neg ( prob P E ) ) )
                )
              )
              /\
              (
                ( A.e E
                  ( A.e F
                    (
                      ( prob P ( inter E F ) )
                      =R
                      ( mul ( cprob Q E F ) ( prob P F ) )
                    )
                  )
                )
                /\
                (
                  ( A.e E
                    ( A.e F
                      (
                        ( disjoint E F )
                        ->
                        (
                          ( prob P ( union E F ) )
                          =R
                          ( add ( prob P E ) ( prob P F ) )
                        )
                      )
                    )
                  )
                  /\
                  ( A.e E
                    ( A.el zs
                      (
                        ( pairwise ( consE E zs ) )
                        ->
                        ( disjoint E ( bigUnion zs ) )
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

ev-inter-comm $a |- (
  A.w omega
    (
      ( holds ( inter A B ) omega )
      <->
      ( holds ( inter B A ) omega )
    )
) $.

ev-union-comm $a |- (
  A.w omega
    (
      ( holds ( union A B ) omega )
      <->
      ( holds ( union B A ) omega )
    )
) $.

ev-inter-assoc $a |- (
  A.w omega
    (
      ( holds ( inter ( inter A B ) C ) omega )
      <->
      ( holds ( inter A ( inter B C ) ) omega )
    )
) $.

ev-union-assoc $a |- (
  A.w omega
    (
      ( holds ( union ( union A B ) C ) omega )
      <->
      ( holds ( union A ( union B C ) ) omega )
    )
) $.

ev-inter-distrib-left $a |- (
  A.w omega
    (
      ( holds ( inter A ( union B C ) ) omega )
      <->
      (
        holds
          ( union ( inter A B ) ( inter A C ) )
          omega
      )
    )
) $.

${
  source-axioms-probability-context-hyp
    $e |- ( ProbContext P Q ) $.

  ${
    indep-compl-both-hyp $e |- ( indep P A B ) $.

    indep-compl-both $a |- (
      indep P ( compl A ) ( compl B )
    ) $.
  $}

  inclusion-exclusion-three $a |- (
    ( prob P ( union ( union A B ) C ) )
    =R
    (
      add
        ( prob P A )
        (
          add
            ( prob P B )
            (
              add
                ( prob P C )
                (
                  neg
                    (
                      add
                        ( prob P ( inter A B ) )
                        (
                          add
                            ( prob P ( inter A C ) )
                            (
                              add
                                ( prob P ( inter B C ) )
                                (
                                  neg
                                    (
                                      prob
                                        P
                                        ( inter ( inter A B ) C )
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
  probability-context-hyp $e |- ( ProbContext P Q ) $.

  prob-union-comm $a |- (
    ( prob P ( union A B ) )
    =R
    ( prob P ( union B A ) )
  ) $.

  prob-union-idem $a |- (
    ( prob P ( union A A ) )
    =R
    ( prob P A )
  ) $.

  prob-diff $a |- (
    ( prob P ( diff A B ) )
    =R
    (
      add
        ( prob P A )
        ( neg ( prob P ( inter A B ) ) )
    )
  ) $.

  bayes-symm $a |- (
    ( mul ( cprob Q A B ) ( prob P B ) )
    =R
    ( mul ( cprob Q B A ) ( prob P A ) )
  ) $.

  law-total-prob $a |- (
    ( prob P A )
    =R
    (
      add
        ( mul ( cprob Q A B ) ( prob P B ) )
        (
          mul
            ( cprob Q A ( compl B ) )
            ( prob P ( compl B ) )
        )
    )
  ) $.

  ${
    prob-union-indep-hyp $e |- ( indep P A B ) $.

    prob-union-indep $a |- (
      ( prob P ( union A B ) )
      =R
      (
        add
          ( prob P A )
          (
            add
              ( prob P B )
              (
                neg
                  ( mul ( prob P A ) ( prob P B ) )
              )
          )
      )
    ) $.
  $}

  ${
    indep-compl-right-hyp $e |- ( indep P A B ) $.

    indep-compl-right $a |- (
      indep P A ( compl B )
    ) $.
  $}

  ${
    indep-symm-hyp $e |- ( indep P A B ) $.

    indep-symm $a |- (
      indep P B A
    ) $.
  $}

  ${
    indep-compl-left-hyp $e |- ( indep P A B ) $.

    indep-compl-left $a |- (
      indep P ( compl A ) B
    ) $.
  $}

  ${
    prob-big-union-disjoint-hyp $e |- ( pairwise xs ) $.

    prob-big-union-disjoint $a |- (
      ( prob P ( bigUnion xs ) )
      =R
      ( foldAdd ( mapProb P xs ) )
    ) $.
  $}

  ${
    prob-big-union-zero-pairwise-hyp $e |- ( pairwise xs ) $.
    prob-big-union-zero-members-hyp $e |- (
      A.e E
        (
          ( inE E xs )
          ->
          ( ( prob P E ) =R zero )
        )
    ) $.

    prob-big-union-disjoint-zero $a |- (
      ( prob P ( bigUnion xs ) ) =R zero
    ) $.
  $}

$}
