$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/defunctionalization_Defunctionalization_continue_2qtvc: the
  defunctionalized continuation verification condition states the recursive
  size decrease for each continuation constructor and preservation of the
  inductively generated continuation-evaluation relation. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  E and T are exactly the source finite inductive carriers of arithmetic
  expressions and continuations. Their tagged constructors are disjoint and
  injective; closure, exhaustiveness, and structural induction exclude both
  missing constructor trees and extraneous non-well-founded values.

  F is direct expression evaluation, G is expression size, and H is
  continuation size. Their displayed equations are the complete recursive
  definitions over E and T. R is exactly the least ternary relation on
  T x ZZ x ZZ closed under the three source eval_cont introduction rules.

  The source match on c is expanded into the three disjoint constructor
  cases. In each A1 or A2 branch its constructor fields remain existentially
  scoped inside that case, while result retains its universal integer scope.
  All source integers remain elements of the full SetMM integer class ZZ.
  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCCte NTP4VCSub
  NTP4VCI NTP4VCA1 NTP4VCA2
  NTP4VCEval NTP4VCEvalClosed
$.

ntp4vc-cte-syntax $a class ( NTP4VCCte A ) $.
ntp4vc-sub-syntax $a class ( NTP4VCSub A B ) $.
ntp4vc-i-syntax $a class NTP4VCI $.
ntp4vc-a1-syntax $a class ( NTP4VCA1 A B ) $.
ntp4vc-a2-syntax $a class ( NTP4VCA2 A B ) $.

ntp4vc-eval-syntax
  $a wff ( NTP4VCEval A B C D ) $.
ntp4vc-eval-closed-syntax
  $a wff ( NTP4VCEvalClosed A B C D ) $.

ntp4vc-cte-definition $a |- (
  NTP4VCCte A
) = <. 0 , A >. $.

ntp4vc-sub-definition $a |- (
  NTP4VCSub A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-i-definition $a |- NTP4VCI = <. 0 , (/) >. $.

ntp4vc-a1-definition $a |- (
  NTP4VCA1 A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-a2-definition $a |- (
  NTP4VCA2 A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-eval-definition $a |- (
  ( NTP4VCEval A B C D )
  <->
  <. B , <. C , D >. >. e. A
) $.

${
  $d e k r v w A B C D $.

  ntp4vc-eval-closed-definition $a |- (
    ( NTP4VCEvalClosed A B C D )
    <->
    (
      A. v e. ZZ A. k e. C A. e e. B A. r e. ZZ
        (
          ( NTP4VCEval A ( NTP4VCA2 v k ) ( D ` e ) r )
          ->
          ( NTP4VCEval A ( NTP4VCA1 e k ) v r )
        )
      /\
      (
        A. k e. C A. w e. ZZ A. v e. ZZ A. r e. ZZ
          (
            ( NTP4VCEval A k ( w - v ) r )
            ->
            ( NTP4VCEval A ( NTP4VCA2 w k ) v r )
          )
        /\
        A. v e. ZZ
          ( NTP4VCEval A NTP4VCI v v )
      )
    )
  ) $.
$}

${
  $d e k n q r s v w x y
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite inductive expression carrier. $)
  ntp4vc-expr-cte-closure $e |- A. n e. ZZ
    ( NTP4VCCte n ) e. E $.

  ntp4vc-expr-sub-closure $e |- A. x e. E A. y e. E
    ( NTP4VCSub x y ) e. E $.

  ntp4vc-expr-constructor-exhaustive $e |- A. e e. E
    (
      E. n e. ZZ e = ( NTP4VCCte n )
      \/
      E. x e. E E. y e. E
        e = ( NTP4VCSub x y )
    ) $.

  ntp4vc-expr-structural-induction $e |- A. s e. ~P E
    (
      (
        A. n e. ZZ
          ( NTP4VCCte n ) e. s
        /\
        A. x e. E A. y e. E
          (
            (
              x e. s
              /\
              y e. s
            )
            ->
            ( NTP4VCSub x y ) e. s
          )
      )
      ->
      s = E
    ) $.

  $( Complete recursive expression evaluation and size definitions. $)
  ntp4vc-direct-eval-function $e |- F e. ( ZZ ^m E ) $.
  ntp4vc-size-e-function $e |- G e. ( ZZ ^m E ) $.

  ntp4vc-direct-eval-cte $e |- A. n e. ZZ
    ( F ` ( NTP4VCCte n ) ) = n $.

  ntp4vc-direct-eval-sub $e |- A. x e. E A. y e. E
    (
      F ` ( NTP4VCSub x y )
    )
    =
    (
      ( F ` x )
      -
      ( F ` y )
    ) $.

  ntp4vc-size-e-cte $e |- A. n e. ZZ
    ( G ` ( NTP4VCCte n ) ) = 1 $.

  ntp4vc-size-e-sub $e |- A. x e. E A. y e. E
    (
      G ` ( NTP4VCSub x y )
    )
    =
    (
      ( 3 + ( G ` x ) )
      +
      ( G ` y )
    ) $.

  $( Exact finite inductive continuation carrier. $)
  ntp4vc-cont-i-closure $e |- NTP4VCI e. T $.

  ntp4vc-cont-a1-closure $e |- A. e e. E A. k e. T
    ( NTP4VCA1 e k ) e. T $.

  ntp4vc-cont-a2-closure $e |- A. v e. ZZ A. k e. T
    ( NTP4VCA2 v k ) e. T $.

  ntp4vc-cont-constructor-exhaustive $e |- A. q e. T
    (
      q = NTP4VCI
      \/
      (
        E. e e. E E. k e. T
          q = ( NTP4VCA1 e k )
        \/
        E. v e. ZZ E. k e. T
          q = ( NTP4VCA2 v k )
      )
    ) $.

  ntp4vc-cont-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCI e. s
        /\
        (
          A. e e. E A. k e. T
            (
              k e. s
              ->
              ( NTP4VCA1 e k ) e. s
            )
          /\
          A. v e. ZZ A. k e. T
            (
              k e. s
              ->
              ( NTP4VCA2 v k ) e. s
            )
        )
      )
      ->
      s = T
    ) $.

  $( Complete recursive continuation-size definition. $)
  ntp4vc-size-c-function $e |- H e. ( ZZ ^m T ) $.

  ntp4vc-size-c-i $e |- ( H ` NTP4VCI ) = 0 $.

  ntp4vc-size-c-a1 $e |- A. e e. E A. k e. T
    (
      H ` ( NTP4VCA1 e k )
    )
    =
    (
      ( 2 + ( G ` e ) )
      +
      ( H ` k )
    ) $.

  ntp4vc-size-c-a2 $e |- A. v e. ZZ A. k e. T
    (
      H ` ( NTP4VCA2 v k )
    )
    =
    (
      1
      +
      ( H ` k )
    ) $.

  $( Exact least relation generated by the three eval_cont rules. $)
  ntp4vc-eval-relation-type $e |- R C_
    ( T X. ( ZZ X. ZZ ) ) $.

  ntp4vc-eval-relation-closed $e |-
    ( NTP4VCEvalClosed R E T F ) $.

  ntp4vc-eval-relation-least $e |- A. q e.
    ~P ( T X. ( ZZ X. ZZ ) )
    (
      ( NTP4VCEvalClosed q E T F )
      ->
      R C_ q
    ) $.

  $( Source theorem parameters c and v. $)
  ntp4vc-c-continuation $e |- A e. T $.
  ntp4vc-v-integer $e |- B e. ZZ $.

  ntp4vc-pearl-defunctionalization-continue-2-vc $a |- (
    (
      (
        E. e e. E E. k e. T
          (
            A = ( NTP4VCA1 e k )
            /\
            (
              0 <_ ( H ` A )
              /\
              (
                (
                  ( H ` ( NTP4VCA2 B k ) )
                  +
                  ( G ` e )
                )
                <
                ( H ` A )
              )
            )
          )
        \/
        E. w e. ZZ E. k e. T
          (
            A = ( NTP4VCA2 w k )
            /\
            (
              0 <_ ( H ` A )
              /\
              ( H ` k ) < ( H ` A )
            )
          )
      )
      \/
      A = NTP4VCI
    )
    /\
    A. r e. ZZ
      (
        (
          (
            E. e e. E E. k e. T
              (
                A = ( NTP4VCA1 e k )
                /\
                (
                  NTP4VCEval
                    R ( NTP4VCA2 B k ) ( F ` e ) r
                )
              )
            \/
            E. w e. ZZ E. k e. T
              (
                A = ( NTP4VCA2 w k )
                /\
                ( NTP4VCEval R k ( w - B ) r )
              )
          )
          \/
          (
            A = NTP4VCI
            /\
            r = B
          )
        )
        ->
        ( NTP4VCEval R A B r )
      )
  ) $.
$}
