$(
  Statement-only formalization of "Puiseux's Theorem" from Hundred Theorems
  item 041: formal Puiseux series over an algebraically closed field of
  characteristic zero are algebraically closed. This file contains no proof.
$)

$(
  The coefficient field is explicitly quantified.  Second-order graph
  comprehension represents every rational-indexed F-valued function, and
  PuiseuxOver selects exactly those whose support is bounded below and lies
  in (1 / d) Z for one positive natural d.  The standard series operations
  are constructed in the foundational context.  Multiplication is the finite
  Cauchy product; finiteness is expressed by a duplicate-free list enumerating
  exactly the nonzero summands.  Further comprehension clauses represent
  every finitely supported natural-indexed coefficient map in both polynomial
  sorts.  Polynomial evaluation is the recursively defined finite sum, and
  AlgebraicClosed F uses polynomials over the same coefficient field F.

  All declarations are unproved $a statements used to encode the source
  structures and definitions.  There is no $p statement and no proof.
$)

$c
  field coeff nat rat series cpoly ppoly rlist qcrel ncrel nsrel
  npred cpred qpred lpred
  wff |-
  ( )
  -. -> <-> /\ \/
  A.f A.c A.n A.q A.s A.cp A.p A.l A.QC A.NC A.NS
  E.c E.n E.q E.s E.cp E.p E.l
  A.NP A.CP A.QP A.LP
  =C =N =Q =S =L
  zeroN succN natAdd ltN PositiveN NatInductive
  zeroC oneC negC addC mulC invC natCast
  InC Field CharZero
  ccoeff CoeffPolyMap FullCPolySpace
  CPolyOver CDegree cpow cpartial CPolyEvalZero
  AlgebraicClosed
  zeroQ oneQ negQ addQ mulQ invQ natQ leQ IsIntegerQ
  RationalContext
  nilL consL InL NoDupL RListInductive
  scoeff CoeffFunction FullSeriesSpace SeriesOver PuiseuxOver
  zeroS oneS negS addS mulS invS
  convPartial ConvSupportList CauchyCoeff PuiseuxField
  pcoeff SeriesPolyMap FullPPolySpace
  PolyOver PDegree spow partial PEvalZero
$.

$v
  F G
  a b c
  n m k
  q r u
  s t v
  f g
  p h
  L M
  R T
  J K
  H I
  un uc uq ul
  ph ps ch
$.

vF $f field F $.
vG $f field G $.

va $f coeff a $.
vb $f coeff b $.
vc $f coeff c $.

vn $f nat n $.
vm $f nat m $.
vk $f nat k $.

vq $f rat q $.
vr $f rat r $.
vu $f rat u $.

vs $f series s $.
vt $f series t $.
vv $f series v $.

vf $f cpoly f $.
vg $f cpoly g $.

vp $f ppoly p $.
vh $f ppoly h $.

vL $f rlist L $.
vM $f rlist M $.

vR $f qcrel R $.
vT $f qcrel T $.

vJ $f ncrel J $.
vK $f ncrel K $.

vH $f nsrel H $.
vI $f nsrel I $.

vnp $f npred un $.
vcp $f cpred uc $.
vqp $f qpred uq $.
vlp $f lpred ul $.

wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

$d n m k $.
$d q r u $.
$d a b c $.
$d s t v $.
$d L M $.

wi $a wff ( ph -> ps ) $.
wb $a wff ( ph <-> ps ) $.
wa $a wff ( ph /\ ps ) $.
wo $a wff ( ph \/ ps ) $.
wn $a wff ( -. ph ) $.

walf $a wff ( A.f F ph ) $.
walc $a wff ( A.c a ph ) $.
waln $a wff ( A.n n ph ) $.
walq $a wff ( A.q q ph ) $.
wals $a wff ( A.s s ph ) $.
walcp $a wff ( A.cp f ph ) $.
walp $a wff ( A.p p ph ) $.
wall $a wff ( A.l L ph ) $.
walqc $a wff ( A.QC R ph ) $.
walnc $a wff ( A.NC J ph ) $.
walns $a wff ( A.NS H ph ) $.

wexc $a wff ( E.c a ph ) $.
wexn $a wff ( E.n n ph ) $.
wexq $a wff ( E.q q ph ) $.
wexs $a wff ( E.s s ph ) $.
wexcp $a wff ( E.cp f ph ) $.
wexp $a wff ( E.p p ph ) $.
wexl $a wff ( E.l L ph ) $.

walnp $a wff ( A.NP un ph ) $.
walcpr $a wff ( A.CP uc ph ) $.
walqp $a wff ( A.QP uq ph ) $.
wallp $a wff ( A.LP ul ph ) $.

wnpapp $a wff ( un n ) $.
wcpapp $a wff ( uc a ) $.
wqpapp $a wff ( uq q ) $.
wlpapp $a wff ( ul L ) $.
wqcapp $a wff ( R q a ) $.
wncapp $a wff ( J n a ) $.
wnsapp $a wff ( H n s ) $.

weqc $a wff ( a =C b ) $.
weqn $a wff ( n =N m ) $.
weqq $a wff ( q =Q r ) $.
weqs $a wff ( s =S F t ) $.
weql $a wff ( L =L M ) $.

tnzero $a nat zeroN $.
tnsucc $a nat ( succN n ) $.
tnadd $a nat ( natAdd n m ) $.

tczero $a coeff ( zeroC F ) $.
tcone $a coeff ( oneC F ) $.
tcneg $a coeff ( negC F a ) $.
tcadd $a coeff ( addC F a b ) $.
tcmul $a coeff ( mulC F a b ) $.
tcinv $a coeff ( invC F a ) $.
tcnatcast $a coeff ( natCast F n ) $.

tccoeff $a coeff ( ccoeff F f n ) $.
tcpow $a coeff ( cpow F a n ) $.
tcpartial $a coeff ( cpartial F f a n ) $.

tqzero $a rat zeroQ $.
tqone $a rat oneQ $.
tqneg $a rat ( negQ q ) $.
tqadd $a rat ( addQ q r ) $.
tqmul $a rat ( mulQ q r ) $.
tqinv $a rat ( invQ q ) $.
tqnat $a rat ( natQ n ) $.

tlnil $a rlist nilL $.
tlcons $a rlist ( consL q L ) $.

tscoeff $a coeff ( scoeff F s q ) $.
tszero $a series ( zeroS F ) $.
tsone $a series ( oneS F ) $.
tsneg $a series ( negS F s ) $.
tsadd $a series ( addS F s t ) $.
tsmul $a series ( mulS F s t ) $.
tsinv $a series ( invS F s ) $.
tcpartialconv $a coeff ( convPartial F s t q L ) $.

tpcoeff $a series ( pcoeff F p n ) $.
tspow $a series ( spow F s n ) $.
tspartial $a series ( partial F p s n ) $.

wlt $a wff ( ltN n m ) $.
wpositive $a wff ( PositiveN n ) $.
wnatind $a wff NatInductive $.

winc $a wff ( InC a F ) $.
wfield $a wff ( Field F ) $.
wcharzero $a wff ( CharZero F ) $.

wcpoly $a wff ( CPolyOver f F ) $.
wcoeffpolymap $a wff ( CoeffPolyMap J F ) $.
wfullcpoly $a wff ( FullCPolySpace F ) $.
wcdegree $a wff ( CDegree f n F ) $.
wcpevalzero $a wff ( CPolyEvalZero f a F ) $.
walgclosed $a wff ( AlgebraicClosed F ) $.

wleq $a wff ( leQ q r ) $.
wintegerq $a wff ( IsIntegerQ q ) $.
wratcontext $a wff RationalContext $.

winl $a wff ( InL q L ) $.
wnodupl $a wff ( NoDupL L ) $.
wlistind $a wff RListInductive $.

wseriesover $a wff ( SeriesOver s F ) $.
wcoefffunction $a wff ( CoeffFunction R F ) $.
wfullseries $a wff ( FullSeriesSpace F ) $.
wpuiseuxover $a wff ( PuiseuxOver s F ) $.
wconvsupport $a wff ( ConvSupportList F s t q L ) $.
wcauchy $a wff ( CauchyCoeff F s t q a ) $.
wpuiseuxfield $a wff ( PuiseuxField F ) $.

wpolyover $a wff ( PolyOver p F ) $.
wseriespolymap $a wff ( SeriesPolyMap H F ) $.
wfullppoly $a wff ( FullPPolySpace F ) $.
wpdegree $a wff ( PDegree p n F ) $.
wpevalzero $a wff ( PEvalZero p s F ) $.

$(
  Typed equalities are Leibniz equality.  Series equality is pointwise
  equality at the one explicit coefficient field F; it never compares
  interpretations at unrelated fields.
$)
coeff-equality-definition $a |- (
  ( a =C b ) <-> ( A.CP uc ( ( uc a ) <-> ( uc b ) ) )
) $.
nat-equality-definition $a |- (
  ( n =N m ) <-> ( A.NP un ( ( un n ) <-> ( un m ) ) )
) $.
rat-equality-definition $a |- (
  ( q =Q r ) <-> ( A.QP uq ( ( uq q ) <-> ( uq r ) ) )
) $.
list-equality-definition $a |- (
  ( L =L M ) <-> ( A.LP ul ( ( ul L ) <-> ( ul M ) ) )
) $.
series-equality-definition $a |- (
  ( s =S F t ) <->
  ( A.q q ( ( scoeff F s q ) =C ( scoeff F t q ) ) )
) $.

$(
  The natural numbers and rational-exponent lists are free inductive sorts.
$)
nat-inductive-definition $a |- (
  NatInductive <->
  (
    ( A.n n ( -. ( ( succN n ) =N zeroN ) ) )
    /\
    (
      ( A.n n ( A.n m (
        ( ( succN n ) =N ( succN m ) ) -> ( n =N m )
      ) ) )
      /\
      ( A.NP un (
        (
          ( un zeroN )
          /\
          ( A.n n ( ( un n ) -> ( un ( succN n ) ) ) )
        )
        ->
        ( A.n n ( un n ) )
      ) )
    )
  )
) $.

nat-add-zero $a |- ( ( natAdd zeroN m ) =N m ) $.
nat-add-successor $a |- (
  ( natAdd ( succN n ) m ) =N ( succN ( natAdd n m ) )
) $.

nat-less-definition $a |- (
  ( ltN n m ) <->
  ( E.n k ( m =N ( succN ( natAdd n k ) ) ) )
) $.

positive-natural-definition $a |- (
  ( PositiveN n ) <-> ( ltN zeroN n )
) $.

list-inductive-definition $a |- (
  RListInductive <->
  (
    ( A.q q ( A.l L (
      -. ( ( consL q L ) =L nilL )
    ) ) )
    /\
    (
      ( A.q q ( A.q r ( A.l L ( A.l M (
        ( ( consL q L ) =L ( consL r M ) )
        ->
        ( ( q =Q r ) /\ ( L =L M ) )
      ) ) ) ) )
      /\
      ( A.LP ul (
        (
          ( ul nilL )
          /\
          ( A.q q ( A.l L (
            ( ul L ) -> ( ul ( consL q L ) )
          ) ) )
        )
        ->
        ( A.l L ( ul L ) )
      ) )
    )
  )
) $.

list-membership-nil $a |- ( -. ( InL q nilL ) ) $.
list-membership-cons $a |- (
  ( InL q ( consL r L ) ) <->
  ( ( q =Q r ) \/ ( InL q L ) )
) $.
list-nodup-nil $a |- ( NoDupL nilL ) $.
list-nodup-cons $a |- (
  ( NoDupL ( consL q L ) ) <->
  ( ( -. ( InL q L ) ) /\ ( NoDupL L ) )
) $.

$(
  Field F is a nontrivial commutative field on exactly the elements InC _ F.
  Every operation is indexed by F, so no operation can silently change the
  coefficient field.
$)
field-definition $a |- (
  ( Field F ) <->
  (
    ( ( InC ( zeroC F ) F ) /\ ( InC ( oneC F ) F ) )
    /\
    (
      ( -. ( ( zeroC F ) =C ( oneC F ) ) )
      /\
      (
        ( A.c a (
          ( InC a F )
          ->
          (
            ( InC ( negC F a ) F )
            /\
            ( InC ( invC F a ) F )
          )
        ) )
        /\
        (
          ( A.c a ( A.c b (
            ( ( InC a F ) /\ ( InC b F ) )
            ->
            (
              ( InC ( addC F a b ) F )
              /\
              ( InC ( mulC F a b ) F )
            )
          ) ) )
          /\
          (
            ( A.c a ( A.c b (
              ( ( InC a F ) /\ ( InC b F ) )
              ->
              ( ( addC F a b ) =C ( addC F b a ) )
            ) ) )
            /\
            (
              ( A.c a ( A.c b ( A.c c (
                (
                  ( InC a F )
                  /\
                  ( ( InC b F ) /\ ( InC c F ) )
                )
                ->
                (
                  ( addC F ( addC F a b ) c )
                  =C
                  ( addC F a ( addC F b c ) )
                )
              ) ) ) )
              /\
              (
                ( A.c a (
                  ( InC a F )
                  ->
                  ( ( addC F a ( zeroC F ) ) =C a )
                ) )
                /\
                (
                  ( A.c a (
                    ( InC a F )
                    ->
                    ( ( addC F a ( negC F a ) ) =C ( zeroC F ) )
                  ) )
                  /\
                  (
                    ( A.c a ( A.c b (
                      ( ( InC a F ) /\ ( InC b F ) )
                      ->
                      ( ( mulC F a b ) =C ( mulC F b a ) )
                    ) ) )
                    /\
                    (
                      ( A.c a ( A.c b ( A.c c (
                        (
                          ( InC a F )
                          /\
                          ( ( InC b F ) /\ ( InC c F ) )
                        )
                        ->
                        (
                          ( mulC F ( mulC F a b ) c )
                          =C
                          ( mulC F a ( mulC F b c ) )
                        )
                      ) ) ) )
                      /\
                      (
                        ( A.c a (
                          ( InC a F )
                          ->
                          ( ( mulC F a ( oneC F ) ) =C a )
                        ) )
                        /\
                        (
                          ( A.c a (
                            (
                              ( InC a F )
                              /\
                              ( -. ( a =C ( zeroC F ) ) )
                            )
                            ->
                            (
                              ( mulC F a ( invC F a ) )
                              =C
                              ( oneC F )
                            )
                          ) )
                          /\
                          ( A.c a ( A.c b ( A.c c (
                            (
                              ( InC a F )
                              /\
                              ( ( InC b F ) /\ ( InC c F ) )
                            )
                            ->
                            (
                              ( mulC F a ( addC F b c ) )
                              =C
                              ( addC F
                                ( mulC F a b )
                                ( mulC F a c )
                              )
                            )
                          ) ) ) )
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

nat-cast-zero $a |- (
  ( natCast F zeroN ) =C ( zeroC F )
) $.
nat-cast-successor $a |- (
  ( natCast F ( succN n ) )
  =C
  ( addC F ( natCast F n ) ( oneC F ) )
) $.

characteristic-zero-definition $a |- (
  ( CharZero F ) <->
  ( A.n n (
    ( PositiveN n )
    ->
    ( -. ( ( natCast F n ) =C ( zeroC F ) ) )
  ) )
) $.

$(
  AlgebraicClosed F is the usual positive-degree polynomial root property
  over F.  CoeffPolyMap J F is an equality-extensional, total, single-valued,
  eventually-zero natural-indexed coefficient graph.  FullCPolySpace F gives
  every such graph a coefficient-polynomial representative.
$)
coefficient-polynomial-map-definition $a |- (
  ( CoeffPolyMap J F ) <->
  (
    ( A.n n ( E.c a (
      ( InC a F )
      /\
      ( J n a )
    ) ) )
    /\
    (
      ( A.n n ( A.c a (
        ( J n a )
        ->
        ( InC a F )
      ) ) )
      /\
      (
        ( A.n n ( A.c a ( A.c b (
          (
            ( J n a )
            /\
            ( J n b )
          )
          ->
          ( a =C b )
        ) ) ) )
        /\
        (
          ( A.n n ( A.c a ( A.c b (
            (
              ( J n a )
              /\
              ( a =C b )
            )
            ->
            ( J n b )
          ) ) ) )
          /\
          ( E.n n ( A.n m (
            ( ltN n m )
            ->
            ( J m ( zeroC F ) )
          ) ) )
        )
      )
    )
  )
) $.

coefficient-polynomial-definition $a |- (
  ( CPolyOver f F ) <->
  (
    ( A.n n ( InC ( ccoeff F f n ) F ) )
    /\
    ( E.n n ( A.n m (
      ( ltN n m )
      ->
      ( ( ccoeff F f m ) =C ( zeroC F ) )
    ) ) )
  )
) $.

full-coefficient-polynomial-space-definition $a |- (
  ( FullCPolySpace F ) <->
  ( A.NC J (
    ( CoeffPolyMap J F )
    ->
    ( E.cp f (
      ( CPolyOver f F )
      /\
      ( A.n n ( A.c a (
        ( J n a )
        <->
        ( ( ccoeff F f n ) =C a )
      ) ) )
    ) )
  ) )
) $.

full-coefficient-polynomial-space-foundation $a |- (
  A.f F ( FullCPolySpace F )
) $.

coefficient-degree-definition $a |- (
  ( CDegree f n F ) <->
  (
    ( CPolyOver f F )
    /\
    (
      ( -. ( ( ccoeff F f n ) =C ( zeroC F ) ) )
      /\
      ( A.n m (
        ( ltN n m )
        ->
        ( ( ccoeff F f m ) =C ( zeroC F ) )
      ) )
    )
  )
) $.

coefficient-power-zero $a |- (
  ( cpow F a zeroN ) =C ( oneC F )
) $.
coefficient-power-successor $a |- (
  ( cpow F a ( succN n ) )
  =C
  ( mulC F ( cpow F a n ) a )
) $.

coefficient-evaluation-zero $a |- (
  ( cpartial F f a zeroN ) =C ( ccoeff F f zeroN )
) $.
coefficient-evaluation-successor $a |- (
  ( cpartial F f a ( succN n ) )
  =C
  ( addC F
    ( cpartial F f a n )
    ( mulC F
      ( ccoeff F f ( succN n ) )
      ( cpow F a ( succN n ) )
    )
  )
) $.

coefficient-polynomial-root-definition $a |- (
  ( CPolyEvalZero f a F ) <->
  ( E.n n (
    ( CDegree f n F )
    /\
    ( ( cpartial F f a n ) =C ( zeroC F ) )
  ) )
) $.

algebraically-closed-definition $a |- (
  ( AlgebraicClosed F ) <->
  ( A.cp f (
    (
      ( CPolyOver f F )
      /\
      ( E.n n (
        ( PositiveN n )
        /\
        ( CDegree f n F )
      ) )
    )
    ->
    ( E.c a (
      ( InC a F )
      /\
      ( CPolyEvalZero f a F )
    ) )
  ) )
) $.

$(
  RationalContext characterizes the ordered field of rational exponents:
  it is an ordered field generated by the natural embedding, and every
  element is a signed quotient of naturals with positive denominator.
$)
integer-rational-definition $a |- (
  ( IsIntegerQ q ) <->
  ( E.n n (
    ( q =Q ( natQ n ) )
    \/
    ( q =Q ( negQ ( natQ n ) ) )
  ) )
) $.

rational-context-definition $a |- (
  RationalContext <->
  (
    ( NatInductive /\ RListInductive )
    /\
    (
      ( -. ( zeroQ =Q oneQ ) )
      /\
      (
        ( A.n n (
          ( natQ ( succN n ) )
          =Q
          ( addQ ( natQ n ) oneQ )
        ) )
        /\
        (
          ( ( natQ zeroN ) =Q zeroQ )
          /\
          (
            ( A.q q ( A.q r (
              ( addQ q r ) =Q ( addQ r q )
            ) ) )
            /\
            (
              ( A.q q ( A.q r ( A.q u (
                ( addQ ( addQ q r ) u )
                =Q
                ( addQ q ( addQ r u ) )
              ) ) ) )
              /\
              (
                ( A.q q ( ( addQ q zeroQ ) =Q q ) )
                /\
                (
                  ( A.q q (
                    ( addQ q ( negQ q ) ) =Q zeroQ
                  ) )
                  /\
                  (
                    ( A.q q ( A.q r (
                      ( mulQ q r ) =Q ( mulQ r q )
                    ) ) )
                    /\
                    (
                      ( A.q q ( A.q r ( A.q u (
                        ( mulQ ( mulQ q r ) u )
                        =Q
                        ( mulQ q ( mulQ r u ) )
                      ) ) ) )
                      /\
                      (
                        ( A.q q ( ( mulQ q oneQ ) =Q q ) )
                        /\
                        (
                          ( A.q q (
                            ( -. ( q =Q zeroQ ) )
                            ->
                            (
                              ( mulQ q ( invQ q ) )
                              =Q
                              oneQ
                            )
                          ) )
                          /\
                          (
                            ( A.q q ( A.q r ( A.q u (
                              ( mulQ q ( addQ r u ) )
                              =Q
                              ( addQ
                                ( mulQ q r )
                                ( mulQ q u )
                              )
                            ) ) ) )
                            /\
                            (
                              ( A.q q ( leQ q q ) )
                              /\
                              (
                                ( A.q q ( A.q r (
                                  (
                                    ( leQ q r )
                                    /\
                                    ( leQ r q )
                                  )
                                  ->
                                  ( q =Q r )
                                ) ) )
                                /\
                                (
                                  ( A.q q ( A.q r ( A.q u (
                                    (
                                      ( leQ q r )
                                      /\
                                      ( leQ r u )
                                    )
                                    ->
                                    ( leQ q u )
                                  ) ) ) )
                                  /\
                                  (
                                    ( A.q q ( A.q r (
                                      ( leQ q r )
                                      \/
                                      ( leQ r q )
                                    ) ) )
                                    /\
                                    (
                                      ( A.q q ( A.q r ( A.q u (
                                        ( leQ q r )
                                        ->
                                        (
                                          leQ
                                          ( addQ q u )
                                          ( addQ r u )
                                        )
                                      ) ) ) )
                                      /\
                                      (
                                        ( A.q q ( A.q r (
                                          (
                                            ( leQ zeroQ q )
                                            /\
                                            ( leQ zeroQ r )
                                          )
                                          ->
                                          (
                                            leQ
                                            zeroQ
                                            ( mulQ q r )
                                          )
                                        ) ) )
                                        /\
                                        ( A.q q (
                                          E.n n ( E.n m (
                                            ( PositiveN m )
                                            /\
                                            (
                                              (
                                                q
                                                =Q
                                                ( mulQ
                                                  ( natQ n )
                                                  ( invQ ( natQ m ) )
                                                )
                                              )
                                              \/
                                              (
                                                q
                                                =Q
                                                ( negQ
                                                  ( mulQ
                                                    ( natQ n )
                                                    ( invQ ( natQ m ) )
                                                  )
                                                )
                                              )
                                            )
                                          ) )
                                        ) )
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
    )
  )
) $.

$(
  These declarations fix the natural and rational syntactic sorts as the
  standard foundational domains.  They are not hypotheses of Puiseux's
  theorem.
$)
natural-domain-foundation $a |- NatInductive $.
rational-domain-foundation $a |- RationalContext $.

$(
  CoeffFunction R F says that the second-order graph R is a total,
  single-valued rational-indexed function into F.  FullSeriesSpace F is a
  genuine comprehension/surjectivity principle: every such graph has a
  series representative, and that representative has exactly the graph's
  coefficients.  Thus the primitive series syntax cannot denote only a
  proper subcollection of the full function space (rat -> F).
$)
coefficient-function-definition $a |- (
  ( CoeffFunction R F ) <->
  (
    ( A.q q ( E.c a (
      ( InC a F )
      /\
      ( R q a )
    ) ) )
    /\
    (
      ( A.q q ( A.c a (
        ( R q a )
        ->
        ( InC a F )
      ) ) )
      /\
      ( A.q q ( A.c a ( A.c b (
        (
          ( R q a )
          /\
          ( R q b )
        )
        ->
        ( a =C b )
      ) ) ) )
    )
  )
) $.

full-series-space-definition $a |- (
  ( FullSeriesSpace F ) <->
  ( A.QC R (
    ( CoeffFunction R F )
    ->
    ( E.s s (
      ( A.q q ( A.c a (
        ( R q a )
        <->
        ( ( scoeff F s q ) =C a )
      ) ) )
    ) )
  ) )
) $.

full-series-space-foundation $a |- (
  A.f F ( FullSeriesSpace F )
) $.

$(
  PuiseuxOver s F is therefore the full subtype of rational-indexed
  F-valued functions satisfying the exact support condition: support is
  bounded below, and multiplication by one positive natural denominator
  sends every supported exponent to an integer.
$)
series-over-definition $a |- (
  ( SeriesOver s F ) <->
  ( A.q q ( InC ( scoeff F s q ) F ) )
) $.

puiseux-series-definition $a |- (
  ( PuiseuxOver s F ) <->
  (
    ( SeriesOver s F )
    /\
    ( E.q r ( E.n n (
      ( PositiveN n )
      /\
      ( A.q q (
        ( -. ( ( scoeff F s q ) =C ( zeroC F ) ) )
        ->
        (
          ( leQ r q )
          /\
          ( IsIntegerQ ( mulQ q ( natQ n ) ) )
        )
      ) )
    ) ) )
  )
) $.

$(
  The list L in ConvSupportList enumerates exactly the nonzero summands
  coeff(s,r) * coeff(t,q-r).  convPartial recursively adds those summands,
  so CauchyCoeff is the ordinary finite Cauchy coefficient without replacing
  a series by a finite table.
$)
convolution-support-definition $a |- (
  ( ConvSupportList F s t q L ) <->
  (
    ( NoDupL L )
    /\
    ( A.q r (
      ( InL r L )
      <->
      (
        -.
        (
          ( mulC F
            ( scoeff F s r )
            ( scoeff F t ( addQ q ( negQ r ) ) )
          )
          =C
          ( zeroC F )
        )
      )
    ) )
  )
) $.

convolution-sum-nil $a |- (
  ( convPartial F s t q nilL ) =C ( zeroC F )
) $.
convolution-sum-cons $a |- (
  ( convPartial F s t q ( consL r L ) )
  =C
  ( addC F
    ( mulC F
      ( scoeff F s r )
      ( scoeff F t ( addQ q ( negQ r ) ) )
    )
    ( convPartial F s t q L )
  )
) $.

cauchy-coefficient-definition $a |- (
  ( CauchyCoeff F s t q a ) <->
  ( E.l L (
    ( ConvSupportList F s t q L )
    /\
    ( a =C ( convPartial F s t q L ) )
  ) )
) $.

$(
  PuiseuxField F fixes the standard coefficientwise zero, one, negation and
  addition, the Cauchy product above, closure on the exact Puiseux carrier,
  and the commutative-field laws.  Its inverse is thereby the unique field
  inverse for the Cauchy multiplication.
$)
puiseux-field-definition $a |- (
  ( PuiseuxField F ) <->
  (
    ( ( PuiseuxOver ( zeroS F ) F )
      /\
      ( PuiseuxOver ( oneS F ) F )
    )
    /\
    (
      ( A.q q (
        ( ( scoeff F ( zeroS F ) q ) =C ( zeroC F ) )
        /\
        (
          (
            ( q =Q zeroQ )
            ->
            ( ( scoeff F ( oneS F ) q ) =C ( oneC F ) )
          )
          /\
          (
            ( -. ( q =Q zeroQ ) )
            ->
            ( ( scoeff F ( oneS F ) q ) =C ( zeroC F ) )
          )
        )
      ) )
      /\
      (
        ( A.s s (
          ( PuiseuxOver s F )
          ->
          (
            ( PuiseuxOver ( negS F s ) F )
            /\
            ( A.q q (
              ( scoeff F ( negS F s ) q )
              =C
              ( negC F ( scoeff F s q ) )
            ) )
          )
        ) )
        /\
        (
          ( A.s s (
            (
              ( PuiseuxOver s F )
              /\
              ( -. ( s =S F ( zeroS F ) ) )
            )
            ->
            ( PuiseuxOver ( invS F s ) F )
          ) )
          /\
          (
            ( A.s s ( A.s t (
              (
                ( PuiseuxOver s F )
                /\
                ( PuiseuxOver t F )
              )
              ->
              (
                ( PuiseuxOver ( addS F s t ) F )
                /\
                (
                  ( PuiseuxOver ( mulS F s t ) F )
                  /\
                  ( A.q q (
                    (
                      ( scoeff F ( addS F s t ) q )
                      =C
                      ( addC F
                        ( scoeff F s q )
                        ( scoeff F t q )
                      )
                    )
                    /\
                    ( E.c a (
                      ( CauchyCoeff F s t q a )
                      /\
                      ( ( scoeff F ( mulS F s t ) q ) =C a )
                    ) )
                  ) )
                )
              )
            ) ) )
            /\
            (
              ( -. ( ( zeroS F ) =S F ( oneS F ) ) )
              /\
              (
                ( A.s s ( A.s t (
                  (
                    ( PuiseuxOver s F )
                    /\
                    ( PuiseuxOver t F )
                  )
                  ->
                  ( ( addS F s t ) =S F ( addS F t s ) )
                ) ) )
                /\
                (
                  ( A.s s ( A.s t ( A.s v (
                    (
                      ( PuiseuxOver s F )
                      /\
                      (
                        ( PuiseuxOver t F )
                        /\
                        ( PuiseuxOver v F )
                      )
                    )
                    ->
                    (
                      ( addS F ( addS F s t ) v )
                      =S F
                      ( addS F s ( addS F t v ) )
                    )
                  ) ) ) )
                  /\
                  (
                    ( A.s s (
                      ( PuiseuxOver s F )
                      ->
                      ( ( addS F s ( zeroS F ) ) =S F s )
                    ) )
                    /\
                    (
                      ( A.s s (
                        ( PuiseuxOver s F )
                        ->
                        (
                          ( addS F s ( negS F s ) )
                          =S F
                          ( zeroS F )
                        )
                      ) )
                      /\
                      (
                        ( A.s s ( A.s t (
                          (
                            ( PuiseuxOver s F )
                            /\
                            ( PuiseuxOver t F )
                          )
                          ->
                          ( ( mulS F s t ) =S F ( mulS F t s ) )
                        ) ) )
                        /\
                        (
                          ( A.s s ( A.s t ( A.s v (
                            (
                              ( PuiseuxOver s F )
                              /\
                              (
                                ( PuiseuxOver t F )
                                /\
                                ( PuiseuxOver v F )
                              )
                            )
                            ->
                            (
                              ( mulS F ( mulS F s t ) v )
                              =S F
                              ( mulS F s ( mulS F t v ) )
                            )
                          ) ) ) )
                          /\
                          (
                            ( A.s s (
                              ( PuiseuxOver s F )
                              ->
                              ( ( mulS F s ( oneS F ) ) =S F s )
                            ) )
                            /\
                            (
                              ( A.s s (
                                (
                                  ( PuiseuxOver s F )
                                  /\
                                  ( -. ( s =S F ( zeroS F ) ) )
                                )
                                ->
                                (
                                  ( mulS F s ( invS F s ) )
                                  =S F
                                  ( oneS F )
                                )
                              ) )
                              /\
                              ( A.s s ( A.s t ( A.s v (
                                (
                                  ( PuiseuxOver s F )
                                  /\
                                  (
                                    ( PuiseuxOver t F )
                                    /\
                                    ( PuiseuxOver v F )
                                  )
                                )
                                ->
                                (
                                  ( mulS F s ( addS F t v ) )
                                  =S F
                                  ( addS F
                                    ( mulS F s t )
                                    ( mulS F s v )
                                  )
                                )
                              ) ) ) )
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

$(
  This is the foundational construction clause for the standard Puiseux
  field on the full function space above.  It supplies the explicitly
  defined operations and their closure/field laws for every coefficient
  field; it is not an additional premise of the final theorem and contains
  no polynomial-root or algebraic-closedness assertion.
$)
puiseux-field-foundation $a |- (
  A.f F (
    ( Field F )
    ->
    ( PuiseuxField F )
  )
) $.

$(
  SeriesPolyMap H F is the analogous equality-extensional, total,
  single-valued, eventually-zero graph with Puiseux-series values.
  FullPPolySpace F gives every such graph a polynomial representative.
$)
series-polynomial-map-definition $a |- (
  ( SeriesPolyMap H F ) <->
  (
    ( A.n n ( E.s s (
      ( PuiseuxOver s F )
      /\
      ( H n s )
    ) ) )
    /\
    (
      ( A.n n ( A.s s (
        ( H n s )
        ->
        ( PuiseuxOver s F )
      ) ) )
      /\
      (
        ( A.n n ( A.s s ( A.s t (
          (
            ( H n s )
            /\
            ( H n t )
          )
          ->
          ( s =S F t )
        ) ) ) )
        /\
        (
          ( A.n n ( A.s s ( A.s t (
            (
              ( H n s )
              /\
              ( s =S F t )
            )
            ->
            ( H n t )
          ) ) ) )
          /\
          ( E.n n ( A.n m (
            ( ltN n m )
            ->
            ( H m ( zeroS F ) )
          ) ) )
        )
      )
    )
  )
) $.

polynomial-definition $a |- (
  ( PolyOver p F ) <->
  (
    ( A.n n ( PuiseuxOver ( pcoeff F p n ) F ) )
    /\
    ( E.n n ( A.n m (
      ( ltN n m )
      ->
      ( ( pcoeff F p m ) =S F ( zeroS F ) )
    ) ) )
  )
) $.

full-puiseux-polynomial-space-definition $a |- (
  ( FullPPolySpace F ) <->
  ( A.NS H (
    ( SeriesPolyMap H F )
    ->
    ( E.p p (
      ( PolyOver p F )
      /\
      ( A.n n ( A.s s (
        ( H n s )
        <->
        ( ( pcoeff F p n ) =S F s )
      ) ) )
    ) )
  ) )
) $.

full-puiseux-polynomial-space-foundation $a |- (
  A.f F ( FullPPolySpace F )
) $.

$(
  PDegree is the greatest nonzero coefficient index.  partial is the finite
  evaluation sum, and PEvalZero means that this evaluation is the zero
  Puiseux series.
$)
polynomial-degree-definition $a |- (
  ( PDegree p n F ) <->
  (
    ( PolyOver p F )
    /\
    (
      ( -. ( ( pcoeff F p n ) =S F ( zeroS F ) ) )
      /\
      ( A.n m (
        ( ltN n m )
        ->
        ( ( pcoeff F p m ) =S F ( zeroS F ) )
      ) )
    )
  )
) $.

series-power-zero $a |- (
  ( spow F s zeroN ) =S F ( oneS F )
) $.
series-power-successor $a |- (
  ( spow F s ( succN n ) )
  =S F
  ( mulS F ( spow F s n ) s )
) $.

polynomial-evaluation-zero $a |- (
  ( partial F p s zeroN ) =S F ( pcoeff F p zeroN )
) $.
polynomial-evaluation-successor $a |- (
  ( partial F p s ( succN n ) )
  =S F
  ( addS F
    ( partial F p s n )
    ( mulS F
      ( pcoeff F p ( succN n ) )
      ( spow F s ( succN n ) )
    )
  )
) $.

polynomial-root-definition $a |- (
  ( PEvalZero p s F ) <->
  ( E.n n (
    ( PDegree p n F )
    /\
    ( ( partial F p s n ) =S F ( zeroS F ) )
  ) )
) $.

$(
  Puiseux's Theorem.  The foundational declarations above construct the
  fixed natural, rational, full series, and standard Puiseux-field domains.
  The theorem's assumptions are exactly that F is a field, has
  characteristic zero, and is algebraically closed.
$)
puiseux-series-algebraically-closed $a |- (
  ( A.f F (
    (
      ( Field F )
      /\
      (
        ( CharZero F )
        /\
        ( AlgebraicClosed F )
      )
    )
    ->
    ( A.p p (
      (
        ( PolyOver p F )
        /\
        ( E.n n (
          ( PositiveN n )
          /\
          ( PDegree p n F )
        ) )
      )
      ->
      ( E.s s (
        ( PuiseuxOver s F )
        /\
        ( PEvalZero p s F )
      ) )
    ) )
  ) )
) $.
