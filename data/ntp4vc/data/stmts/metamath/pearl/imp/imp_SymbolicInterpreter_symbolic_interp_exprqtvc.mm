$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_exprqtvc: constructor-wise
  correctness of symbolic interpretation for integer literals, program
  variables, and subtraction, including unbound-variable propagation and
  provenance of symbolic variables. This file contains no proof.
$)

$(
  The many-sorted grammar gives the source's arbitrary program-variable,
  symbolic-variable, constraint, finite-variable-set, and raw symbolic-state
  domains, and the exact inductive expression and symbolic-expression
  constructor trees. Integer values range over the full integer sort.

  Compose is characterized pointwise by the source definition using the
  state's rho and sigma/get observations. Constr and Vars expose the remaining
  sym_state fields, and StateValid is exactly the source record invariant:
  vars_in_constraint constr is included in vars, and every symbolic variable
  in the range of sigma belongs to vars. SInterp and InVars are the complete
  recursive definitions of symbolic-expression interpretation and variable
  membership. Eval is the least relation closed under the six constructors
  of ConcreteSemantics.eval_expr. Mapped and SymOK only factor source
  subformulas.

  The final assertion expands the source match over the three expression
  constructors. Its two constructor-identification disjunctions are the
  direct reductions of the nested source matches. The final $a declaration
  is Metamath's native unproved statement encoding; every preceding $a is
  syntax or a faithful definition, and this database contains no $p proof
  declaration.
$)

$c
  pvar int expr svar symexpr constr varset state
  sopt iopt behavior environment evalrel
  wff |-
  ( ) = -> /\ \/ <-> -. A.i A.x A.e A.v A.y A.d A.r A.t E.x E.v
  Elit Evar Esub Slit Svar Ssub
  SomeS NoneS SomeI NoneI Get Rho Constr Vars ConstraintVars InSet
  Compose Lookup SInterp InVars StateValid
  Enormal Eunbound Eval Rel Closed Mapped SymOK -
$.

$v
  x x1 n m e e1 e2 v u se se1 se2 c vs s q q1 p p1 b env R ph ps
$.

pvar-x $f pvar x $.
pvar-x1 $f pvar x1 $.

int-n $f int n $.
int-m $f int m $.

expr-e $f expr e $.
expr-e1 $f expr e1 $.
expr-e2 $f expr e2 $.

svar-v $f svar v $.
svar-u $f svar u $.

symexpr-se $f symexpr se $.
symexpr-se1 $f symexpr se1 $.
symexpr-se2 $f symexpr se2 $.

constr-c $f constr c $.
varset-vs $f varset vs $.
state-s $f state s $.

sopt-q $f sopt q $.
sopt-q1 $f sopt q1 $.
iopt-p $f iopt p $.
iopt-p1 $f iopt p1 $.

behavior-b $f behavior b $.
environment-env $f environment env $.
evalrel-R $f evalrel R $.

wff-ph $f wff ph $.
wff-ps $f wff ps $.

expr-literal $a expr ( Elit n ) $.
expr-variable $a expr ( Evar x ) $.
expr-subtraction $a expr ( Esub e1 e2 ) $.

symbolic-literal $a symexpr ( Slit n ) $.
symbolic-variable $a symexpr ( Svar v ) $.
symbolic-subtraction $a symexpr ( Ssub se1 se2 ) $.

svar-option-some $a sopt ( SomeS v ) $.
svar-option-none $a sopt NoneS $.
int-option-some $a iopt ( SomeI n ) $.
int-option-none $a iopt NoneI $.

state-get $a sopt ( Get s x ) $.
state-rho $a int ( Rho s v ) $.
state-constr $a constr ( Constr s ) $.
state-vars $a varset ( Vars s ) $.
constraint-vars $a varset ( ConstraintVars c ) $.
finite-set-membership $a wff ( InSet v vs ) $.
state-compose $a environment ( Compose s ) $.
environment-lookup $a iopt ( Lookup env x ) $.

symbolic-interpretation $a int ( SInterp s se ) $.
symbolic-variable-membership $a wff ( InVars v se ) $.

behavior-normal $a behavior ( Enormal n ) $.
behavior-unbound $a behavior Eunbound $.

integer-subtraction $a int ( n - m ) $.

integer-equality $a wff ( n = m ) $.
expression-equality $a wff ( e1 = e2 ) $.
symbolic-variable-equality $a wff ( v = u ) $.
svar-option-equality $a wff ( q = q1 ) $.
int-option-equality $a wff ( p = p1 ) $.

implication $a wff ( ph -> ps ) $.
conjunction $a wff ( ph /\ ps ) $.
disjunction $a wff ( ph \/ ps ) $.
biconditional $a wff ( ph <-> ps ) $.
negation $a wff ( -. ph ) $.

integer-forall $a wff ( A.i n ph ) $.
program-variable-forall $a wff ( A.x x ph ) $.
expression-forall $a wff ( A.e e ph ) $.
symbolic-variable-forall $a wff ( A.v v ph ) $.
symbolic-expression-forall $a wff ( A.y se ph ) $.
environment-forall $a wff ( A.d env ph ) $.
eval-relation-forall $a wff ( A.r R ph ) $.
state-forall $a wff ( A.t s ph ) $.
program-variable-exists $a wff ( E.x x ph ) $.
symbolic-variable-exists $a wff ( E.v v ph ) $.

relation-application $a wff ( Rel R env e b ) $.
evaluation-application $a wff ( Eval env e b ) $.
closed-application $a wff ( Closed R ) $.
mapped-application $a wff ( Mapped s se ) $.
symbolically-correct-application $a wff ( SymOK s e se ) $.
state-valid-application $a wff ( StateValid s ) $.

$(
  Exact sym_state record invariant. The varset sort denotes the source's
  finite Svar.set carrier, so InSet is its membership observation.
$)
state-valid-definition $a |- (
  ( StateValid s )
  <->
  (
    ( A.v v (
      ( InSet v ( ConstraintVars ( Constr s ) ) )
      ->
      ( InSet v ( Vars s ) )
    ) )
    /\
    ( A.x x ( A.v v (
      (
        ( Get s x )
        =
        ( SomeS v )
      )
      ->
      ( InSet v ( Vars s ) )
    ) ) )
  )
) $.

$(
  These two clauses are exactly compose rho sigma x after observing rho and
  get through the symbolic state.
$)
compose-some-definition $a |- (
  (
    ( Lookup ( Compose s ) x )
    =
    ( SomeI n )
  )
  <->
  ( E.v v (
    (
      ( Get s x )
      =
      ( SomeS v )
    )
    /\
    ( n = ( Rho s v ) )
  ) )
) $.

compose-none-definition $a |- (
  (
    ( Lookup ( Compose s ) x )
    =
    NoneI
  )
  <->
  (
    ( Get s x )
    =
    NoneS
  )
) $.

$(
  Complete recursive equations for interp_symbolic_expr.
$)
symbolic-interpret-literal-definition $a |- (
  ( SInterp s ( Slit n ) )
  =
  n
) $.

symbolic-interpret-variable-definition $a |- (
  ( SInterp s ( Svar v ) )
  =
  ( Rho s v )
) $.

symbolic-interpret-subtraction-definition $a |- (
  ( SInterp s ( Ssub se1 se2 ) )
  =
  (
    ( SInterp s se1 )
    -
    ( SInterp s se2 )
  )
) $.

$(
  Complete recursive membership equations for vars_in_symbolic_expr.
$)
symbolic-vars-literal-definition $a |- (
  -. ( InVars v ( Slit n ) )
) $.

symbolic-vars-variable-definition $a |- (
  ( InVars v ( Svar u ) )
  <->
  ( v = u )
) $.

symbolic-vars-subtraction-definition $a |- (
  ( InVars v ( Ssub se1 se2 ) )
  <->
  (
    ( InVars v se1 )
    \/
    ( InVars v se2 )
  )
) $.

$(
  Closed R says that R contains every constructor clause of eval_expr.
$)
closed-definition $a |- (
  ( Closed R )
  <->
  (
    ( A.d env ( A.i n
      ( Rel R env ( Elit n ) ( Enormal n ) )
    ) )
    /\
    (
      ( A.d env ( A.x x ( A.i n (
        (
          ( Lookup env x )
          =
          ( SomeI n )
        )
        ->
        ( Rel R env ( Evar x ) ( Enormal n ) )
      ) ) ) )
      /\
      (
        ( A.d env ( A.x x (
          (
            ( Lookup env x )
            =
            NoneI
          )
          ->
          ( Rel R env ( Evar x ) Eunbound )
        ) ) )
        /\
        (
          ( A.d env ( A.e e1 ( A.i n ( A.e e2 ( A.i m (
            (
              ( Rel R env e1 ( Enormal n ) )
              /\
              ( Rel R env e2 ( Enormal m ) )
            )
            ->
            (
              Rel R env ( Esub e1 e2 )
                ( Enormal ( n - m ) )
            )
          ) ) ) ) ) )
          /\
          (
            ( A.d env ( A.e e1 ( A.e e2 (
              ( Rel R env e1 Eunbound )
              ->
              ( Rel R env ( Esub e1 e2 ) Eunbound )
            ) ) ) )
            /\
            ( A.d env ( A.e e1 ( A.i n ( A.e e2 (
              (
                ( Rel R env e1 ( Enormal n ) )
                /\
                ( Rel R env e2 Eunbound )
              )
              ->
              ( Rel R env ( Esub e1 e2 ) Eunbound )
            ) ) ) ) )
          )
        )
      )
    )
  )
) $.

$(
  Intersection of all closed relations is the least inductively generated
  evaluation relation.
$)
evaluation-definition $a |- (
  ( Eval env e b )
  <->
  ( A.r R (
    ( Closed R )
    ->
    ( Rel R env e b )
  ) )
) $.

mapped-definition $a |- (
  ( Mapped s se )
  <->
  ( A.v v (
    ( InVars v se )
    ->
    ( E.x x (
      ( Get s x )
      =
      ( SomeS v )
    ) )
  ) )
) $.

symbolically-correct-definition $a |- (
  ( SymOK s e se )
  <->
  (
    (
      Eval
        ( Compose s )
        e
        ( Enormal ( SInterp s se ) )
    )
    /\
    ( Mapped s se )
  )
) $.

$(
  Constructor-wise expansion of symbolic_interp_expr'vc.
$)
ntp4vc-pearl-imp-symbolic-interpreter-symbolic-interp-expr-vc $a |- (
  A.t s (
    ( StateValid s )
    ->
    (
      ( A.i n
        ( SymOK s ( Elit n ) ( Slit n ) )
      )
      /\
      (
        ( A.x x (
          (
            ( A.v u (
              (
                ( Get s x )
                =
                ( SomeS u )
              )
              ->
              ( SymOK s ( Evar x ) ( Svar u ) )
            ) )
            /\
            (
              ( Get s x )
              =
              NoneS
            )
            ->
            ( Eval ( Compose s ) ( Evar x ) Eunbound )
          )
        ) )
        /\
        ( A.e e1 ( A.e e2 (
          (
            ( e1 = e2 )
            \/
            ( e2 = e2 )
          )
          /\
          (
            ( A.y se1 (
              ( SymOK s e2 se1 )
              ->
              (
                (
                  ( e1 = e1 )
                  \/
                  ( e2 = e1 )
                )
                /\
                (
                  ( A.y se2 (
                    ( SymOK s e1 se2 )
                    ->
                    (
                      SymOK
                        s
                        ( Esub e1 e2 )
                        ( Ssub se2 se1 )
                    )
                  ) )
                  /\
                  (
                    ( Eval ( Compose s ) e1 Eunbound )
                    ->
                    (
                      Eval
                        ( Compose s )
                        ( Esub e1 e2 )
                        Eunbound
                    )
                  )
                )
              )
            ) )
            /\
            (
              ( Eval ( Compose s ) e2 Eunbound )
              ->
              (
                Eval
                  ( Compose s )
                  ( Esub e1 e2 )
                  Eunbound
              )
            )
          )
        ) ) )
      )
    )
  )
) $.
