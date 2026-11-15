$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_eval_2qtvc: the
  reduction-semantics evaluation verification condition states the recursive
  size decrease for each evaluation-context constructor and preservation of
  direct evaluation under context recomposition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  E and C are exactly the source inductive carriers of finite arithmetic-
  expression and evaluation-context constructor trees. Their tagged
  constructors are disjoint and injective; closure, exhaustiveness, and
  structural induction exclude missing constructor trees, extraneous values,
  and non-well-founded constructor objects.

  F is direct integer evaluation, G is expression size, H is context size,
  and P is context recomposition. Their displayed equations are the complete
  recursive definitions over E and C. The source match on c is expanded into
  its three disjoint constructor cases, with constructor fields existentially
  scoped inside their cases and result universally scoped over the full SetMM
  integer class ZZ. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
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
  $d c e n q r s x y
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

  $( Complete recursive expression-size definition. $)
  ntp4vc-size-e-function $e |- G e. ( ZZ ^m E ) $.

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

  $( Complete recursive evaluation-context-size definition. $)
  ntp4vc-size-c-function $e |- H e. ( ZZ ^m C ) $.

  ntp4vc-size-c-empty $e |-
    ( H ` NTP4VCEmpty ) = 0 $.

  ntp4vc-size-c-left $e |- A. c e. C A. e e. E
    (
      H ` ( NTP4VCLeft c e )
    )
    =
    (
      ( 2 + ( H ` c ) )
      +
      ( G ` e )
    ) $.

  ntp4vc-size-c-right $e |- A. n e. ZZ A. c e. C
    (
      H ` ( NTP4VCRight n c )
    )
    =
    (
      1
      +
      ( H ` c )
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

  $( Source theorem parameters c and n. $)
  ntp4vc-c-context $e |- A e. C $.
  ntp4vc-n-integer $e |- B e. ZZ $.

  ntp4vc-pearl-defunctionalization-reduction-semantics-eval-2-vc
    $a |- (
      (
        A = NTP4VCEmpty
        \/
        (
          E. c e. C E. e e. E
            (
              A = ( NTP4VCLeft c e )
              /\
              (
                0
                <_
                (
                  1
                  +
                  ( 2 x. ( H ` A ) )
                )
                /\
                (
                  2
                  x.
                  (
                    (
                      H ` ( NTP4VCRight B c )
                    )
                    +
                    ( G ` e )
                  )
                )
                <
                (
                  1
                  +
                  ( 2 x. ( H ` A ) )
                )
              )
            )
          \/
          E. n e. ZZ E. c e. C
            (
              A = ( NTP4VCRight n c )
              /\
              (
                0
                <_
                (
                  1
                  +
                  ( 2 x. ( H ` A ) )
                )
                /\
                (
                  2
                  x.
                  (
                    ( H ` c )
                    +
                    (
                      G
                      `
                      ( NTP4VCCte ( n - B ) )
                    )
                  )
                )
                <
                (
                  1
                  +
                  ( 2 x. ( H ` A ) )
                )
              )
            )
        )
      )
      /\
      A. r e. ZZ
        (
          (
            (
              A = NTP4VCEmpty
              /\
              r = B
            )
            \/
            (
              E. c e. C E. e e. E
                (
                  A = ( NTP4VCLeft c e )
                  /\
                  r
                  =
                  (
                    F
                    `
                    (
                      P
                      `
                      <. ( NTP4VCRight B c ) , e >.
                    )
                  )
                )
              \/
              E. n e. ZZ E. c e. C
                (
                  A = ( NTP4VCRight n c )
                  /\
                  r
                  =
                  (
                    F
                    `
                    (
                      P
                      `
                      <. c , ( NTP4VCCte ( n - B ) ) >.
                    )
                  )
                )
            )
          )
          ->
          r
          =
          (
            F
            `
            (
              P
              `
              <. A , ( NTP4VCCte B ) >.
            )
          )
        )
    ) $.
$}
