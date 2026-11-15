$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/imp/imp_ConcreteInterpreter_interp_exprqtvc: constructor-wise
  correctness of the concrete interpreter for integer expressions with
  possibly unbound program variables. This file contains no proof.
$)

$(
  The environment sort represents Imperative.t program_var int. Lookup is
  both model1 application and get, since get is definitionally model1 in the
  sources. Eval is defined below as the least relation closed under the six
  constructors of ConcreteSemantics.eval_expr. The final assertion expands
  the source match on the three constructors of Syntax.expr.
$)

$c
  pvar int expr opt behavior environment evalrel wff |-
  ( ) = -> /\ \/ <-> A.i A.x A.e A.d A.r
  Elit Evar Esub Some None Lookup Enormal Eunbound
  Eval Rel Closed -
$.

$v
  x n m result o1 o2 e e1 e2 q q1 b env R
  ph ps
$.

pvar-x $f pvar x $.

int-n $f int n $.
int-m $f int m $.
int-result $f int result $.
int-o1 $f int o1 $.
int-o2 $f int o2 $.

expr-e $f expr e $.
expr-e1 $f expr e1 $.
expr-e2 $f expr e2 $.

opt-q $f opt q $.
opt-q1 $f opt q1 $.

behavior-b $f behavior b $.
environment-env $f environment env $.
evalrel-R $f evalrel R $.

wff-ph $f wff ph $.
wff-ps $f wff ps $.

expr-literal $a expr ( Elit n ) $.
expr-variable $a expr ( Evar x ) $.
expr-subtraction $a expr ( Esub e1 e2 ) $.

option-some $a opt ( Some n ) $.
option-none $a opt None $.
environment-lookup $a opt ( Lookup env x ) $.

behavior-normal $a behavior ( Enormal n ) $.
behavior-unbound $a behavior Eunbound $.

integer-subtraction $a int ( n - m ) $.

integer-equality $a wff ( n = m ) $.
expression-equality $a wff ( e1 = e2 ) $.
option-equality $a wff ( q = q1 ) $.

implication $a wff ( ph -> ps ) $.
conjunction $a wff ( ph /\ ps ) $.
disjunction $a wff ( ph \/ ps ) $.
biconditional $a wff ( ph <-> ps ) $.

integer-forall $a wff ( A.i n ph ) $.
program-variable-forall $a wff ( A.x x ph ) $.
expression-forall $a wff ( A.e e ph ) $.
environment-forall $a wff ( A.d env ph ) $.
eval-relation-forall $a wff ( A.r R ph ) $.

relation-application $a wff ( Rel R env e b ) $.
evaluation-application $a wff ( Eval env e b ) $.
closed-application $a wff ( Closed R ) $.

$(
  Closed R says that R contains each constructor clause of eval_expr.
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
        ( ( Lookup env x ) = ( Some n ) )
        ->
        ( Rel R env ( Evar x ) ( Enormal n ) )
      ) ) ) )
      /\
      (
        ( A.d env ( A.x x (
          ( ( Lookup env x ) = None )
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
            ( Rel R env ( Esub e1 e2 ) ( Enormal ( n - m ) ) )
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
  This intersection-of-closed-relations definition is the standard
  second-order encoding of the least inductively generated evaluation
  relation.
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

$(
  Constructor-wise expansion of interp_expr'vc. For an option-valued lookup,
  the source match returning result = v in the Some v case and False in the
  None case is equivalently written Lookup env x = Some result.
$)
interp-expr-vc $a |- (
  A.d env (
    ( A.i n
      ( Eval env ( Elit n ) ( Enormal n ) )
    )
    /\
    (
      ( A.x x (
        (
          ( A.i result (
            ( ( Lookup env x ) = ( Some result ) )
            ->
            ( Eval env ( Evar x ) ( Enormal result ) )
          ) )
          /\
          (
            ( ( Lookup env x ) = None )
            ->
            ( Eval env ( Evar x ) Eunbound )
          )
        )
      ) )
      /\
      ( A.e e1 ( A.e e2 (
        ( ( e1 = e2 ) \/ ( e2 = e2 ) )
        /\
        (
          ( A.i o1 (
            ( Eval env e2 ( Enormal o1 ) )
            ->
            (
              ( ( e1 = e1 ) \/ ( e2 = e1 ) )
              /\
              (
                ( A.i o2 (
                  ( Eval env e1 ( Enormal o2 ) )
                  ->
                  ( Eval env ( Esub e1 e2 )
                    ( Enormal ( o2 - o1 ) ) )
                ) )
                /\
                (
                  ( Eval env e1 Eunbound )
                  ->
                  ( Eval env ( Esub e1 e2 ) Eunbound )
                )
              )
            )
          ) )
          /\
          (
            ( Eval env e2 Eunbound )
            ->
            ( Eval env ( Esub e1 e2 ) Eunbound )
          )
        )
      ) ) )
    )
  )
) $.
