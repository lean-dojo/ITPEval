$(
  Statement-only formalization of the Babel-formal polynomial artifact:
  roots, linear factors, products of roots, and the bound on distinct roots
  by polynomial degree. This file contains no proof.
$)

$(
  This many-sorted second-order encoding keeps the source's custom naturals,
  coefficient values, polynomials, and coefficient lists distinct. Binder
  positions have atomic variable-only syntactic classes. Typed equality is
  Leibniz equality, the two ring and polynomial contexts are exact
  biconditional packages, and the inductive objects and predicates use
  free-constructor and least-closure characterizations. Every mathematical
  declaration is an unproved $a statement; there are no $p statements.
$)

$c
  nvar rvar pvar lvar
  nat rterm pterm list
  npred rpred ppred lpred nrel rlrel
  wff |-
  ( )
  Nat_O Nat_S natAdd natLe NatInductive
  zeroR oneR oppR addR mulR
  zeroP oneP oppP addP mulP
  degree monomial eval X C Xminus
  NilL ConsL InL NoDupL lengthL ListInductive PolyRoots Root
  =N =R =P =L
  -. -> <-> /\ \/
  A.n A.r A.p A.l E.r E.p
  A.NP A.RP A.PP A.LP A.NR A.RL
  RingR RingP PolyContext
$.

$v
  nv mv kv av bv cv pv qv rv lv tv
  n m k a b c x y z p q r s xs ys
  un ur up ul unr url ph ps
$.

bn $f nvar nv $.
bm $f nvar mv $.
bk $f nvar kv $.
ba $f rvar av $.
bb $f rvar bv $.
bc $f rvar cv $.
bp $f pvar pv $.
bq $f pvar qv $.
br $f pvar rv $.
bl $f lvar lv $.
bt $f lvar tv $.

vn $f nat n $.
vm $f nat m $.
vk $f nat k $.
ra $f rterm a $.
rb $f rterm b $.
rc $f rterm c $.
rx $f rterm x $.
ry $f rterm y $.
rz $f rterm z $.
pp $f pterm p $.
pq $f pterm q $.
pr $f pterm r $.
ps-poly $f pterm s $.
lxs $f list xs $.
lys $f list ys $.

fnp $f npred un $.
frp $f rpred ur $.
fpp $f ppred up $.
flp $f lpred ul $.
fnr $f nrel unr $.
frl $f rlrel url $.
wph $f wff ph $.
wps $f wff ps $.

$d nv mv kv $.
$d av bv cv $.
$d pv qv rv $.
$d lv tv $.

nat-var-term $a nat nv $.
r-var-term $a rterm av $.
p-var-term $a pterm pv $.
list-var-term $a list lv $.

nat-zero-term $a nat Nat_O $.
nat-succ-term $a nat ( Nat_S n ) $.
nat-add-term $a nat ( natAdd n m ) $.
r-zero-term $a rterm zeroR $.
r-one-term $a rterm oneR $.
r-opp-term $a rterm ( oppR a ) $.
r-add-term $a rterm ( addR a b ) $.
r-mul-term $a rterm ( mulR a b ) $.
p-zero-term $a pterm zeroP $.
p-one-term $a pterm oneP $.
p-opp-term $a pterm ( oppP p ) $.
p-add-term $a pterm ( addP p q ) $.
p-mul-term $a pterm ( mulP p q ) $.
p-degree-term $a nat ( degree p ) $.
p-monomial-term $a pterm ( monomial n a ) $.
p-eval-term $a rterm ( eval p a ) $.
p-x-term $a pterm X $.
p-c-term $a pterm ( C a ) $.
p-xminus-term $a pterm ( Xminus a ) $.
list-nil-term $a list NilL $.
list-cons-term $a list ( ConsL a xs ) $.
list-length-term $a nat ( lengthL xs ) $.
p-roots-term $a pterm ( PolyRoots xs ) $.

nat-pred-app $a wff ( un n ) $.
r-pred-app $a wff ( ur a ) $.
p-pred-app $a wff ( up p ) $.
list-pred-app $a wff ( ul xs ) $.
nat-rel-app $a wff ( unr n m ) $.
rl-rel-app $a wff ( url a xs ) $.

not-formula $a wff ( -. ph ) $.
imp-formula $a wff ( ph -> ps ) $.
iff-formula $a wff ( ph <-> ps ) $.
and-formula $a wff ( ph /\ ps ) $.
or-formula $a wff ( ph \/ ps ) $.

forall-nat-formula $a wff ( A.n nv ph ) $.
forall-r-formula $a wff ( A.r av ph ) $.
forall-p-formula $a wff ( A.p pv ph ) $.
forall-list-formula $a wff ( A.l lv ph ) $.
exists-r-formula $a wff ( E.r av ph ) $.
exists-p-formula $a wff ( E.p pv ph ) $.
forall-npred-formula $a wff ( A.NP un ph ) $.
forall-rpred-formula $a wff ( A.RP ur ph ) $.
forall-ppred-formula $a wff ( A.PP up ph ) $.
forall-lpred-formula $a wff ( A.LP ul ph ) $.
forall-nrel-formula $a wff ( A.NR unr ph ) $.
forall-rlrel-formula $a wff ( A.RL url ph ) $.

nat-eq-formula $a wff ( n =N m ) $.
r-eq-formula $a wff ( a =R b ) $.
p-eq-formula $a wff ( p =P q ) $.
list-eq-formula $a wff ( xs =L ys ) $.
nat-le-formula $a wff ( natLe n m ) $.
in-list-formula $a wff ( InL a xs ) $.
no-dup-formula $a wff ( NoDupL xs ) $.
root-formula $a wff ( Root a p ) $.
nat-inductive-formula $a wff NatInductive $.
list-inductive-formula $a wff ListInductive $.
ring-r-formula $a wff RingR $.
ring-p-formula $a wff RingP $.
poly-context-formula $a wff PolyContext $.

$(
  Typed Leibniz equality: two terms are equal exactly when every predicate
  of their sort has the same truth value on them.
$)
nat-equality-definition $a |- (
  ( n =N m ) <-> ( A.NP un ( ( un n ) <-> ( un m ) ) )
) $.
r-equality-definition $a |- (
  ( a =R b ) <-> ( A.RP ur ( ( ur a ) <-> ( ur b ) ) )
) $.
p-equality-definition $a |- (
  ( p =P q ) <-> ( A.PP up ( ( up p ) <-> ( up q ) ) )
) $.
list-equality-definition $a |- (
  ( xs =L ys ) <-> ( A.LP ul ( ( ul xs ) <-> ( ul ys ) ) )
) $.

$(
  Explicit reflexivity and congruence give the Leibniz relations their
  required substitution behavior for every operation and predicate below.
$)
nat-equality-reflexive $a |- ( n =N n ) $.
r-equality-reflexive $a |- ( a =R a ) $.
p-equality-reflexive $a |- ( p =P p ) $.
list-equality-reflexive $a |- ( xs =L xs ) $.

${
  nat-succ-congruence-hyp $e |- ( n =N m ) $.
  nat-succ-congruence $a |- ( ( Nat_S n ) =N ( Nat_S m ) ) $.
$}
${
  nat-add-congruence-left-hyp $e |- ( n =N k ) $.
  nat-add-congruence-left $a |- (
    ( natAdd n m ) =N ( natAdd k m )
  ) $.
$}
${
  nat-add-congruence-right-hyp $e |- ( n =N k ) $.
  nat-add-congruence-right $a |- (
    ( natAdd m n ) =N ( natAdd m k )
  ) $.
$}
${
  nat-le-congruence-left-hyp $e |- ( n =N k ) $.
  nat-le-congruence-left $a |- (
    ( natLe n m ) <-> ( natLe k m )
  ) $.
$}
${
  nat-le-congruence-right-hyp $e |- ( n =N k ) $.
  nat-le-congruence-right $a |- (
    ( natLe m n ) <-> ( natLe m k )
  ) $.
$}

${
  r-opp-congruence-hyp $e |- ( a =R b ) $.
  r-opp-congruence $a |- ( ( oppR a ) =R ( oppR b ) ) $.
$}
${
  r-add-congruence-left-hyp $e |- ( a =R c ) $.
  r-add-congruence-left $a |- (
    ( addR a b ) =R ( addR c b )
  ) $.
$}
${
  r-add-congruence-right-hyp $e |- ( a =R c ) $.
  r-add-congruence-right $a |- (
    ( addR b a ) =R ( addR b c )
  ) $.
$}
${
  r-mul-congruence-left-hyp $e |- ( a =R c ) $.
  r-mul-congruence-left $a |- (
    ( mulR a b ) =R ( mulR c b )
  ) $.
$}
${
  r-mul-congruence-right-hyp $e |- ( a =R c ) $.
  r-mul-congruence-right $a |- (
    ( mulR b a ) =R ( mulR b c )
  ) $.
$}

${
  p-opp-congruence-hyp $e |- ( p =P q ) $.
  p-opp-congruence $a |- ( ( oppP p ) =P ( oppP q ) ) $.
$}
${
  p-add-congruence-left-hyp $e |- ( p =P r ) $.
  p-add-congruence-left $a |- (
    ( addP p q ) =P ( addP r q )
  ) $.
$}
${
  p-add-congruence-right-hyp $e |- ( p =P r ) $.
  p-add-congruence-right $a |- (
    ( addP q p ) =P ( addP q r )
  ) $.
$}
${
  p-mul-congruence-left-hyp $e |- ( p =P r ) $.
  p-mul-congruence-left $a |- (
    ( mulP p q ) =P ( mulP r q )
  ) $.
$}
${
  p-mul-congruence-right-hyp $e |- ( p =P r ) $.
  p-mul-congruence-right $a |- (
    ( mulP q p ) =P ( mulP q r )
  ) $.
$}
${
  degree-congruence-hyp $e |- ( p =P q ) $.
  degree-congruence $a |- ( ( degree p ) =N ( degree q ) ) $.
$}
${
  eval-congruence-polynomial-hyp $e |- ( p =P q ) $.
  eval-congruence-polynomial $a |- (
    ( eval p a ) =R ( eval q a )
  ) $.
$}
${
  eval-congruence-value-hyp $e |- ( a =R b ) $.
  eval-congruence-value $a |- (
    ( eval p a ) =R ( eval p b )
  ) $.
$}
${
  monomial-congruence-degree-hyp $e |- ( n =N m ) $.
  monomial-congruence-degree $a |- (
    ( monomial n a ) =P ( monomial m a )
  ) $.
$}
${
  monomial-congruence-coefficient-hyp $e |- ( a =R b ) $.
  monomial-congruence-coefficient $a |- (
    ( monomial n a ) =P ( monomial n b )
  ) $.
$}
${
  c-congruence-hyp $e |- ( a =R b ) $.
  c-congruence $a |- ( ( C a ) =P ( C b ) ) $.
$}
${
  xminus-congruence-hyp $e |- ( a =R b ) $.
  xminus-congruence $a |- ( ( Xminus a ) =P ( Xminus b ) ) $.
$}

${
  list-cons-head-congruence-hyp $e |- ( a =R b ) $.
  list-cons-head-congruence $a |- (
    ( ConsL a xs ) =L ( ConsL b xs )
  ) $.
$}
${
  list-cons-tail-congruence-hyp $e |- ( xs =L ys ) $.
  list-cons-tail-congruence $a |- (
    ( ConsL a xs ) =L ( ConsL a ys )
  ) $.
$}
${
  length-congruence-hyp $e |- ( xs =L ys ) $.
  length-congruence $a |- ( ( lengthL xs ) =N ( lengthL ys ) ) $.
$}
${
  poly-roots-congruence-hyp $e |- ( xs =L ys ) $.
  poly-roots-congruence $a |- (
    ( PolyRoots xs ) =P ( PolyRoots ys )
  ) $.
$}
${
  in-list-value-congruence-hyp $e |- ( a =R b ) $.
  in-list-value-congruence $a |- (
    ( InL a xs ) <-> ( InL b xs )
  ) $.
$}
${
  in-list-list-congruence-hyp $e |- ( xs =L ys ) $.
  in-list-list-congruence $a |- (
    ( InL a xs ) <-> ( InL a ys )
  ) $.
$}
${
  no-dup-congruence-hyp $e |- ( xs =L ys ) $.
  no-dup-congruence $a |- (
    ( NoDupL xs ) <-> ( NoDupL ys )
  ) $.
$}
${
  root-value-congruence-hyp $e |- ( a =R b ) $.
  root-value-congruence $a |- (
    ( Root a p ) <-> ( Root b p )
  ) $.
$}
${
  root-polynomial-congruence-hyp $e |- ( p =P q ) $.
  root-polynomial-congruence $a |- (
    ( Root a p ) <-> ( Root a q )
  ) $.
$}

$(
  The custom natural sort is the free inductive algebra on Nat_O and Nat_S:
  the constructors are disjoint and injective, and every constructor-closed
  predicate contains every natural.
$)
nat-inductive-definition $a |- (
  NatInductive <->
  (
    ( A.n nv ( -. ( ( Nat_S nv ) =N Nat_O ) ) )
    /\
    (
      ( A.n nv ( A.n mv (
        ( ( Nat_S nv ) =N ( Nat_S mv ) ) -> ( nv =N mv )
      ) ) )
      /\
      ( A.NP un (
        (
          ( un Nat_O )
          /\
          ( A.n nv ( ( un nv ) -> ( un ( Nat_S nv ) ) ) )
        )
        ->
        ( A.n nv ( un nv ) )
      ) )
    )
  )
) $.
nat-inductive $a |- NatInductive $.

nat-add-o-def $a |- ( ( natAdd Nat_O m ) =N m ) $.
nat-add-s-def $a |- (
  ( natAdd ( Nat_S n ) m ) =N ( Nat_S ( natAdd n m ) )
) $.

$(
  natLe is the least relation containing reflexivity and closed under the
  source le_S constructor.
$)
nat-le-definition $a |- (
  ( natLe n m ) <->
  ( A.NR unr (
    (
      ( A.n nv ( unr nv nv ) )
      /\
      ( A.n nv ( A.n mv (
        ( unr nv mv ) -> ( unr nv ( Nat_S mv ) )
      ) ) )
    )
    ->
    ( unr n m )
  ) )
) $.

nat-le-refl $a |- ( natLe n n ) $.
${
  nat-le-step-hyp $e |- ( natLe n m ) $.
  nat-le-step $a |- ( natLe n ( Nat_S m ) ) $.
$}
mynat-add-o-left $a |- ( ( natAdd Nat_O m ) =N m ) $.
mynat-add-s-left $a |- (
  ( natAdd ( Nat_S n ) m ) =N ( Nat_S ( natAdd n m ) )
) $.
mynat-zero-le $a |- ( natLe Nat_O n ) $.
mynat-add-zero-r $a |- ( ( natAdd n Nat_O ) =N n ) $.
${
  mynat-succ-le-succ-hyp $e |- ( natLe n m ) $.
  mynat-succ-le-succ $a |- ( natLe ( Nat_S n ) ( Nat_S m ) ) $.
$}
mynat-add-s-r $a |- (
  ( natAdd m ( Nat_S n ) ) =N ( Nat_S ( natAdd m n ) )
) $.
mynat-add-comm $a |- (
  ( natAdd n m ) =N ( natAdd m n )
) $.

$(
  Coefficient lists are the free inductive algebra on NilL and ConsL.
$)
list-inductive-definition $a |- (
  ListInductive <->
  (
    ( A.r av ( A.l lv (
      -. ( ( ConsL av lv ) =L NilL )
    ) ) )
    /\
    (
      ( A.r av ( A.r bv ( A.l lv ( A.l tv (
        ( ( ConsL av lv ) =L ( ConsL bv tv ) )
        ->
        ( ( av =R bv ) /\ ( lv =L tv ) )
      ) ) ) ) )
      /\
      ( A.LP ul (
        (
          ( ul NilL )
          /\
          ( A.r av ( A.l lv (
            ( ul lv ) -> ( ul ( ConsL av lv ) )
          ) ) )
        )
        ->
        ( A.l lv ( ul lv ) )
      ) )
    )
  )
) $.
list-inductive $a |- ListInductive $.

$(
  InL and NoDupL are their source inductive predicates, expressed as
  intersections of all relations or predicates closed under the constructors.
$)
in-list-definition $a |- (
  ( InL a xs ) <->
  ( A.RL url (
    (
      ( A.r av ( A.l lv ( url av ( ConsL av lv ) ) ) )
      /\
      ( A.r av ( A.r bv ( A.l lv (
        ( url av lv ) -> ( url av ( ConsL bv lv ) )
      ) ) ) )
    )
    ->
    ( url a xs )
  ) )
) $.

no-dup-definition $a |- (
  ( NoDupL xs ) <->
  ( A.LP ul (
    (
      ( ul NilL )
      /\
      ( A.r av ( A.l lv (
        (
          ( -. ( InL av lv ) )
          /\
          ( ul lv )
        )
        ->
        ( ul ( ConsL av lv ) )
      ) ) )
    )
    ->
    ( ul xs )
  ) )
) $.

in-list-head $a |- ( InL a ( ConsL a xs ) ) $.
${
  in-list-tail-hyp $e |- ( InL a xs ) $.
  in-list-tail $a |- ( InL a ( ConsL b xs ) ) $.
$}
no-dup-nil $a |- ( NoDupL NilL ) $.
${
  no-dup-cons-not-in-hyp $e |- ( -. ( InL a xs ) ) $.
  no-dup-cons-tail-hyp $e |- ( NoDupL xs ) $.
  no-dup-cons $a |- ( NoDupL ( ConsL a xs ) ) $.
$}
length-nil-def $a |- ( ( lengthL NilL ) =N Nat_O ) $.
length-cons-def $a |- (
  ( lengthL ( ConsL a xs ) ) =N ( Nat_S ( lengthL xs ) )
) $.

$(
  RingR and RingP are definitionally equivalent to exactly the source class
  fields, with all source universal scopes explicit.
$)
ring-r-definition $a |- (
  RingR <->
  (
    ( -. ( oneR =R zeroR ) )
    /\
    (
      ( A.r av ( A.r bv (
        ( addR av bv ) =R ( addR bv av )
      ) ) )
      /\
      (
        ( A.r av ( A.r bv ( A.r cv (
          ( addR ( addR av bv ) cv )
          =R
          ( addR av ( addR bv cv ) )
        ) ) ) )
        /\
        (
          ( A.r av ( ( addR av zeroR ) =R av ) )
          /\
          (
            ( A.r av ( ( addR av ( oppR av ) ) =R zeroR ) )
            /\
            (
              ( A.r av ( A.r bv (
                ( mulR av bv ) =R ( mulR bv av )
              ) ) )
              /\
              (
                ( A.r av ( A.r bv ( A.r cv (
                  ( mulR ( mulR av bv ) cv )
                  =R
                  ( mulR av ( mulR bv cv ) )
                ) ) ) )
                /\
                (
                  ( A.r av ( ( mulR av oneR ) =R av ) )
                  /\
                  (
                    ( A.r av ( A.r bv ( A.r cv (
                      ( mulR av ( addR bv cv ) )
                      =R
                      ( addR ( mulR av bv ) ( mulR av cv ) )
                    ) ) ) )
                    /\
                    (
                      ( A.r av ( ( mulR av zeroR ) =R zeroR ) )
                      /\
                      ( A.r av ( A.r bv (
                        ( ( mulR av bv ) =R zeroR )
                        ->
                        ( ( av =R zeroR ) \/ ( bv =R zeroR ) )
                      ) ) )
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

ring-p-definition $a |- (
  RingP <->
  (
    ( -. ( oneP =P zeroP ) )
    /\
    (
      ( A.p pv ( A.p qv (
        ( addP pv qv ) =P ( addP qv pv )
      ) ) )
      /\
      (
        ( A.p pv ( A.p qv ( A.p rv (
          ( addP ( addP pv qv ) rv )
          =P
          ( addP pv ( addP qv rv ) )
        ) ) ) )
        /\
        (
          ( A.p pv ( ( addP pv zeroP ) =P pv ) )
          /\
          (
            ( A.p pv ( ( addP pv ( oppP pv ) ) =P zeroP ) )
            /\
            (
              ( A.p pv ( A.p qv (
                ( mulP pv qv ) =P ( mulP qv pv )
              ) ) )
              /\
              (
                ( A.p pv ( A.p qv ( A.p rv (
                  ( mulP ( mulP pv qv ) rv )
                  =P
                  ( mulP pv ( mulP qv rv ) )
                ) ) ) )
                /\
                (
                  ( A.p pv ( ( mulP pv oneP ) =P pv ) )
                  /\
                  (
                    ( A.p pv ( A.p qv ( A.p rv (
                      ( mulP pv ( addP qv rv ) )
                      =P
                      ( addP ( mulP pv qv ) ( mulP pv rv ) )
                    ) ) ) )
                    /\
                    (
                      ( A.p pv ( ( mulP pv zeroP ) =P zeroP ) )
                      /\
                      ( A.p pv ( A.p qv (
                        ( ( mulP pv qv ) =P zeroP )
                        ->
                        ( ( pv =P zeroP ) \/ ( qv =P zeroP ) )
                      ) ) )
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

x-def $a |- ( X =P ( monomial ( Nat_S Nat_O ) oneR ) ) $.
c-def $a |- ( ( C a ) =P ( monomial Nat_O a ) ) $.
xminus-def $a |- (
  ( Xminus a ) =P ( addP X ( C ( oppR a ) ) )
) $.
root-def $a |- (
  ( Root a p ) <-> ( ( eval p a ) =R zeroR )
) $.
poly-roots-nil-def $a |- (
  ( PolyRoots NilL ) =P oneP
) $.
poly-roots-cons-def $a |- (
  ( PolyRoots ( ConsL a xs ) )
  =P
  ( mulP ( Xminus a ) ( PolyRoots xs ) )
) $.

$(
  PolyContext is exactly the two source ring structures and every primitive
  polynomial axiom. No additional or hidden assumption is packaged by it.
$)
poly-context-definition $a |- (
  PolyContext <->
  (
    RingR
    /\
    (
      RingP
      /\
      (
        ( ( C zeroR ) =P zeroP )
        /\
        (
          ( ( C oneR ) =P oneP )
          /\
          (
            ( ( degree zeroP ) =N Nat_O )
            /\
            (
              ( A.p pv ( A.p qv ( A.r av (
                ( eval ( addP pv qv ) av )
                =R
                ( addR ( eval pv av ) ( eval qv av ) )
              ) ) ) )
              /\
              (
                ( A.p pv ( A.p qv ( A.r av (
                  ( eval ( mulP pv qv ) av )
                  =R
                  ( mulR ( eval pv av ) ( eval qv av ) )
                ) ) ) )
                /\
                (
                  ( A.r av ( A.r bv (
                    ( eval ( C av ) bv ) =R av
                  ) ) )
                  /\
                  (
                    ( A.r av ( ( eval X av ) =R av ) )
                    /\
                    (
                      ( A.r av (
                        ( -. ( av =R zeroR ) )
                        ->
                        ( ( degree ( C av ) ) =N Nat_O )
                      ) )
                      /\
                      (
                        ( A.p pv (
                          ( ( degree pv ) =N Nat_O )
                          <->
                          ( E.r av ( pv =P ( C av ) ) )
                        ) )
                        /\
                        (
                          ( A.r av (
                            ( degree ( Xminus av ) )
                            =N
                            ( Nat_S Nat_O )
                          ) )
                          /\
                          (
                            ( A.p pv ( A.p qv (
                              (
                                ( -. ( pv =P zeroP ) )
                                /\
                                ( -. ( qv =P zeroP ) )
                              )
                              ->
                              (
                                ( degree ( mulP pv qv ) )
                                =N
                                ( natAdd ( degree pv ) ( degree qv ) )
                              )
                            ) ) )
                            /\
                            ( A.p pv ( A.r av (
                              E.p qv ( E.p rv (
                                (
                                  pv
                                  =P
                                  ( addP
                                    ( mulP qv ( Xminus av ) )
                                    rv
                                  )
                                )
                                /\
                                ( ( degree rv ) =N Nat_O )
                              ) )
                            ) ) )
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

${
  ring-r-hyp $e |- RingR $.
  r-one-neq-zero $a |- ( -. ( oneR =R zeroR ) ) $.
  r-add-comm $a |- ( ( addR a b ) =R ( addR b a ) ) $.
  r-add-assoc $a |- (
    ( addR ( addR a b ) c ) =R ( addR a ( addR b c ) )
  ) $.
  r-add-zero $a |- ( ( addR a zeroR ) =R a ) $.
  r-add-opp $a |- ( ( addR a ( oppR a ) ) =R zeroR ) $.
  r-mul-comm $a |- ( ( mulR a b ) =R ( mulR b a ) ) $.
  r-mul-assoc $a |- (
    ( mulR ( mulR a b ) c ) =R ( mulR a ( mulR b c ) )
  ) $.
  r-mul-one $a |- ( ( mulR a oneR ) =R a ) $.
  r-dist-left $a |- (
    ( mulR a ( addR b c ) )
    =R
    ( addR ( mulR a b ) ( mulR a c ) )
  ) $.
  r-mul-zero $a |- ( ( mulR a zeroR ) =R zeroR ) $.
  r-no-zero-div $a |- (
    ( ( mulR a b ) =R zeroR )
    ->
    ( ( a =R zeroR ) \/ ( b =R zeroR ) )
  ) $.
  ${
    sub-eq-zero-l-hyp $e |- (
      ( addR a ( oppR b ) ) =R zeroR
    ) $.
    sub-eq-zero-l $a |- ( a =R b ) $.
  $}
$}

${
  ring-p-hyp $e |- RingP $.
  p-one-neq-zero $a |- ( -. ( oneP =P zeroP ) ) $.
  p-add-comm $a |- ( ( addP p q ) =P ( addP q p ) ) $.
  p-add-assoc $a |- (
    ( addP ( addP p q ) r ) =P ( addP p ( addP q r ) )
  ) $.
  p-add-zero $a |- ( ( addP p zeroP ) =P p ) $.
  p-add-opp $a |- ( ( addP p ( oppP p ) ) =P zeroP ) $.
  p-mul-comm $a |- ( ( mulP p q ) =P ( mulP q p ) ) $.
  p-mul-assoc $a |- (
    ( mulP ( mulP p q ) r ) =P ( mulP p ( mulP q r ) )
  ) $.
  p-mul-one $a |- ( ( mulP p oneP ) =P p ) $.
  p-dist-left $a |- (
    ( mulP p ( addP q r ) )
    =P
    ( addP ( mulP p q ) ( mulP p r ) )
  ) $.
  p-mul-zero $a |- ( ( mulP p zeroP ) =P zeroP ) $.
  p-no-zero-div $a |- (
    ( ( mulP p q ) =P zeroP )
    ->
    ( ( p =P zeroP ) \/ ( q =P zeroP ) )
  ) $.
$}

${
  poly-context-hyp $e |- PolyContext $.
  context-ring-r $a |- RingR $.
  context-ring-p $a |- RingP $.
  c-zero $a |- ( ( C zeroR ) =P zeroP ) $.
  c-one $a |- ( ( C oneR ) =P oneP ) $.
  deg-zero $a |- ( ( degree zeroP ) =N Nat_O ) $.
  eval-add $a |- (
    ( eval ( addP p q ) a )
    =R
    ( addR ( eval p a ) ( eval q a ) )
  ) $.
  eval-mul $a |- (
    ( eval ( mulP p q ) a )
    =R
    ( mulR ( eval p a ) ( eval q a ) )
  ) $.
  eval-c $a |- ( ( eval ( C c ) a ) =R c ) $.
  eval-x $a |- ( ( eval X a ) =R a ) $.
  deg-c $a |- (
    ( -. ( c =R zeroR ) )
    ->
    ( ( degree ( C c ) ) =N Nat_O )
  ) $.
  deg-constant $a |- (
    ( ( degree p ) =N Nat_O )
    <->
    ( E.r av ( p =P ( C av ) ) )
  ) $.
  deg-xminus $a |- (
    ( degree ( Xminus a ) ) =N ( Nat_S Nat_O )
  ) $.
  deg-mul $a |- (
    (
      ( -. ( p =P zeroP ) )
      /\
      ( -. ( q =P zeroP ) )
    )
    ->
    (
      ( degree ( mulP p q ) )
      =N
      ( natAdd ( degree p ) ( degree q ) )
    )
  ) $.
  euclid-xminus $a |- (
    E.p qv ( E.p rv (
      (
        p =P ( addP ( mulP qv ( Xminus a ) ) rv )
      )
      /\
      ( ( degree rv ) =N Nat_O )
    ) )
  ) $.

  ${
    root-factor-root-hyp $e |- ( Root a p ) $.
    root-factor $a |- (
      E.p qv ( p =P ( mulP qv ( Xminus a ) ) )
    ) $.
  $}

  ${
    root-transfer-factor-hyp $e |- (
      p =P ( mulP q ( Xminus a ) )
    ) $.
    root-transfer-distinct-hyp $e |- ( -. ( b =R a ) ) $.
    root-transfer-root-hyp $e |- ( Root b p ) $.
    root-transfer $a |- ( Root b q ) $.
  $}

  ${
    roots-le-degree-nodup-hyp $e |- ( NoDupL xs ) $.
    roots-le-degree-roots-hyp $e |- (
      A.r av ( ( InL av xs ) -> ( Root av p ) )
    ) $.
    roots-le-degree-nonzero-hyp $e |- ( -. ( p =P zeroP ) ) $.
    roots-le-degree $a |- (
      natLe ( lengthL xs ) ( degree p )
    ) $.
  $}

  xminus-nonzero $a |- ( -. ( ( Xminus a ) =P zeroP ) ) $.

  ${
    constant-root-zero-degree-hyp $e |- (
      ( degree p ) =N Nat_O
    ) $.
    constant-root-zero-root-hyp $e |- ( Root a p ) $.
    constant-root-zero $a |- ( p =P zeroP ) $.
  $}

  ${
    root-of-product-hyp $e |- ( Root a ( mulP p q ) ) $.
    root-of-product $a |- (
      ( Root a p ) \/ ( Root a q )
    ) $.
  $}

  ${
    root-scale-constant-nonzero-hyp $e |- (
      -. ( c =R zeroR )
    ) $.
    root-scale-constant $a |- (
      ( Root a p )
      <->
      ( Root a ( mulP ( C c ) p ) )
    ) $.
  $}

  poly-roots-nonzero $a |- (
    -. ( ( PolyRoots xs ) =P zeroP )
  ) $.

  deg-poly-roots $a |- (
    ( degree ( PolyRoots xs ) ) =N ( lengthL xs )
  ) $.

  ${
    root-factor-list-nodup-hyp $e |- ( NoDupL xs ) $.
    root-factor-list-roots-hyp $e |- (
      A.r av ( ( InL av xs ) -> ( Root av p ) )
    ) $.
    root-factor-list $a |- (
      E.p qv ( p =P ( mulP qv ( PolyRoots xs ) ) )
    ) $.
  $}

  ${
    degree-factorisation-factor-hyp $e |- (
      p =P ( mulP q ( PolyRoots xs ) )
    ) $.
    degree-factorisation-nonzero-hyp $e |- (
      -. ( q =P zeroP )
    ) $.
    degree-factorisation $a |- (
      ( degree p )
      =N
      ( natAdd ( degree q ) ( lengthL xs ) )
    ) $.
  $}
$}
