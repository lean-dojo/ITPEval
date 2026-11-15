$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/defunctionalization_RWithError_interpretqtvc: recomposing an
  arithmetic expression with the empty evaluation context preserves its
  error-aware evaluation result. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  E and C are exactly the source inductive carriers of finite arithmetic
  expression and evaluation-context constructor trees. V is exactly the
  source value carrier consisting of integer results and Underflow. Tagged
  constructors are disjoint and injective; closure, exhaustiveness, and
  structural induction exclude missing constructor trees, extraneous values,
  and non-well-founded constructor objects.

  P is context recomposition and F is error-aware expression evaluation.
  Their displayed equations are the complete recursive definitions over E
  and C. The theorem parameter p remains arbitrary in E, and all source
  integers remain elements of the full SetMM integer class ZZ. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c
  NTP4VCCte NTP4VCSub
  NTP4VCEmpty NTP4VCLeft NTP4VCRight
  NTP4VCVnum NTP4VCUnderflow
$.

ntp4vc-cte-syntax $a class ( NTP4VCCte A ) $.
ntp4vc-sub-syntax $a class ( NTP4VCSub A B ) $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-left-syntax $a class ( NTP4VCLeft A B ) $.
ntp4vc-right-syntax $a class ( NTP4VCRight A B ) $.

ntp4vc-vnum-syntax $a class ( NTP4VCVnum A ) $.
ntp4vc-underflow-syntax $a class NTP4VCUnderflow $.

ntp4vc-cte-definition $a |- (
  NTP4VCCte A
) = <. 0 , A >. $.

ntp4vc-sub-definition $a |- (
  NTP4VCSub A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-empty-definition $a |-
  NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-left-definition $a |- (
  NTP4VCLeft A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-right-definition $a |- (
  NTP4VCRight A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-vnum-definition $a |- (
  NTP4VCVnum A
) = <. 0 , A >. $.

ntp4vc-underflow-definition $a |-
  NTP4VCUnderflow = <. 1 , (/) >. $.

${
  $d c e n q s u v x y
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact inductive expression carrier. $)
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

  $( Exact inductive evaluation-context carrier. $)
  ntp4vc-context-empty-closure $e |-
    NTP4VCEmpty e. C $.

  ntp4vc-context-left-closure $e |- A. c e. C A. e e. E
    ( NTP4VCLeft c e ) e. C $.

  ntp4vc-context-right-closure $e |- A. n e. ZZ A. c e. C
    ( NTP4VCRight n c ) e. C $.

  ntp4vc-context-constructor-exhaustive $e |- A. q e. C
    (
      q = NTP4VCEmpty
      \/
      (
        E. c e. C E. e e. E
          q = ( NTP4VCLeft c e )
        \/
        E. n e. ZZ E. c e. C
          q = ( NTP4VCRight n c )
      )
    ) $.

  ntp4vc-context-structural-induction $e |- A. s e. ~P C
    (
      (
        NTP4VCEmpty e. s
        /\
        (
          A. c e. C A. e e. E
            (
              c e. s
              ->
              ( NTP4VCLeft c e ) e. s
            )
          /\
          A. n e. ZZ A. c e. C
            (
              c e. s
              ->
              ( NTP4VCRight n c ) e. s
            )
        )
      )
      ->
      s = C
    ) $.

  $( Exact error-aware result-value carrier. $)
  ntp4vc-value-vnum-closure $e |- A. n e. ZZ
    ( NTP4VCVnum n ) e. V $.

  ntp4vc-value-underflow-closure $e |-
    NTP4VCUnderflow e. V $.

  ntp4vc-value-constructor-exhaustive $e |- A. v e. V
    (
      E. n e. ZZ v = ( NTP4VCVnum n )
      \/
      v = NTP4VCUnderflow
    ) $.

  $( Complete recursive context-recomposition definition. $)
  ntp4vc-recompose-function $e |-
    P e. ( E ^m ( C X. E ) ) $.

  ntp4vc-recompose-empty $e |- A. e e. E
    (
      P ` <. NTP4VCEmpty , e >.
    )
    =
    e $.

  ntp4vc-recompose-left $e |- A. c e. C A. y e. E A. e e. E
    (
      P ` <. ( NTP4VCLeft c y ) , e >.
    )
    =
    (
      P ` <. c , ( NTP4VCSub e y ) >.
    ) $.

  ntp4vc-recompose-right $e |- A. n e. ZZ A. c e. C A. e e. E
    (
      P ` <. ( NTP4VCRight n c ) , e >.
    )
    =
    (
      P ` <. c , ( NTP4VCSub ( NTP4VCCte n ) e ) >.
    ) $.

  $( Complete recursive error-aware expression-evaluation definition. $)
  ntp4vc-error-eval-function $e |-
    F e. ( V ^m E ) $.

  ntp4vc-error-eval-cte $e |- A. n e. ZZ
    (
      F ` ( NTP4VCCte n )
    )
    =
    if (
      0 <_ n ,
      ( NTP4VCVnum n ) ,
      NTP4VCUnderflow
    ) $.

  ntp4vc-error-eval-sub-left-underflow $e |-
    A. x e. E A. y e. E
      (
        ( F ` x ) = NTP4VCUnderflow
        ->
        (
          F ` ( NTP4VCSub x y )
        )
        =
        NTP4VCUnderflow
      ) $.

  ntp4vc-error-eval-sub-right-underflow $e |-
    A. x e. E A. y e. E A. u e. ZZ
      (
        (
          ( F ` x ) = ( NTP4VCVnum u )
          /\
          ( F ` y ) = NTP4VCUnderflow
        )
        ->
        (
          F ` ( NTP4VCSub x y )
        )
        =
        NTP4VCUnderflow
      ) $.

  ntp4vc-error-eval-sub-numeric $e |-
    A. x e. E A. y e. E A. u e. ZZ A. v e. ZZ
      (
        (
          ( F ` x ) = ( NTP4VCVnum u )
          /\
          ( F ` y ) = ( NTP4VCVnum v )
        )
        ->
        (
          F ` ( NTP4VCSub x y )
        )
        =
        if (
          v <_ u ,
          ( NTP4VCVnum ( u - v ) ) ,
          NTP4VCUnderflow
        )
      ) $.

  $( Source theorem parameter p. $)
  ntp4vc-p-expression $e |- A e. E $.

  ntp4vc-pearl-defunctionalization-rwitherror-interpret-vc $a |- (
    F
    `
    (
      P
      `
      <. NTP4VCEmpty , A >.
    )
  )
  =
  ( F ` A ) $.
$}
