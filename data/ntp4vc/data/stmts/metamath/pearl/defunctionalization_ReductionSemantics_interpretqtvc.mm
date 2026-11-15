$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_interpretqtvc: recomposing an
  arithmetic expression with the empty evaluation context preserves its
  direct integer evaluation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  E and C are exactly the source inductive carriers of finite arithmetic
  expression and evaluation-context constructor trees. Their tagged
  constructors are disjoint and injective; closure, exhaustiveness, and
  structural induction exclude missing constructor trees, extraneous values,
  and non-well-founded constructor objects.

  P is context recomposition and F is direct integer evaluation. Their
  displayed equations are the complete recursive definitions over E and C.
  The theorem parameter p remains arbitrary in E, and all source integers
  remain elements of the full SetMM integer class ZZ. The final $a declaration
  is Metamath's native unproved statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCCte NTP4VCSub
  NTP4VCEmpty NTP4VCLeft NTP4VCRight
$.

ntp4vc-cte-syntax $a class ( NTP4VCCte A ) $.
ntp4vc-sub-syntax $a class ( NTP4VCSub A B ) $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-left-syntax $a class ( NTP4VCLeft A B ) $.
ntp4vc-right-syntax $a class ( NTP4VCRight A B ) $.

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

${
  $d c e n q s x y
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

  $( Complete recursive direct integer-evaluation definition. $)
  ntp4vc-eval-function $e |- F e. ( ZZ ^m E ) $.

  ntp4vc-eval-cte $e |- A. n e. ZZ
    (
      F ` ( NTP4VCCte n )
    )
    =
    n $.

  ntp4vc-eval-sub $e |- A. x e. E A. y e. E
    (
      F ` ( NTP4VCSub x y )
    )
    =
    (
      ( F ` x )
      -
      ( F ` y )
    ) $.

  $( Source theorem parameter p. $)
  ntp4vc-p-expression $e |- A e. E $.

  ntp4vc-pearl-defunctionalization-reduction-semantics-interpret-vc $a |- (
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
