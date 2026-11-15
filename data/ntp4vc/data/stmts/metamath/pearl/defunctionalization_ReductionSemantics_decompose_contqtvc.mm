$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_decompose_contqtvc: the
  reduction-semantics context-decomposition verification condition states the
  recursive size decrease, preservation of redex decompositions under
  recomposition, the empty/value side condition, and construction of the
  subtraction redex in the right-context case. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  E and C are exactly the source inductive carriers of finite arithmetic-
  expression and evaluation-context constructor trees. Their tagged
  constructors are disjoint and injective; closure, exhaustiveness, and
  structural induction exclude missing constructor trees, extraneous values,
  and non-well-founded constructor objects.

  G is expression size, H is context size, and P is context recomposition.
  Their displayed equations are the complete recursive definitions over E
  and C. NTP4VCRedex, NTP4VCValue, and NTP4VCEmptyContext are definitionally
  the source predicates is_a_redex, is_a_value, and is_empty_context.

  The source match on c is expanded into its three disjoint constructor cases.
  Constructor fields remain existentially scoped inside their cases, while
  the redex-decomposition context and expression retain their universal
  scopes. All source integers remain elements of the full SetMM integer class
  ZZ. The final $a declaration is Metamath's native unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCCte NTP4VCSub
  NTP4VCEmpty NTP4VCLeft NTP4VCRight
  NTP4VCRedex NTP4VCValue NTP4VCEmptyContext
$.

ntp4vc-cte-syntax $a class ( NTP4VCCte A ) $.
ntp4vc-sub-syntax $a class ( NTP4VCSub A B ) $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-left-syntax $a class ( NTP4VCLeft A B ) $.
ntp4vc-right-syntax $a class ( NTP4VCRight A B ) $.

ntp4vc-redex-syntax $a wff ( NTP4VCRedex A ) $.
ntp4vc-value-syntax $a wff ( NTP4VCValue A ) $.
ntp4vc-empty-context-syntax
  $a wff ( NTP4VCEmptyContext A ) $.

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
  $d x y A $.

  ntp4vc-redex-definition $a |- (
    ( NTP4VCRedex A )
    <->
    E. x e. ZZ E. y e. ZZ
      A
      =
      (
        NTP4VCSub
          ( NTP4VCCte x )
          ( NTP4VCCte y )
      )
  ) $.
$}

${
  $d x A $.

  ntp4vc-value-definition $a |- (
    ( NTP4VCValue A )
    <->
    E. x e. ZZ
      A = ( NTP4VCCte x )
  ) $.
$}

ntp4vc-empty-context-definition $a |- (
  ( NTP4VCEmptyContext A )
  <->
  A = NTP4VCEmpty
) $.

${
  $d c e n q s w x y
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

  ntp4vc-pearl-defunctionalization-reduction-semantics-decompose-cont-vc
    $a |- (
      (
        A = NTP4VCEmpty
        /\
        ( NTP4VCEmptyContext A )
      )
      \/
      (
        E. c e. C E. e e. E
          (
            A = ( NTP4VCLeft c e )
            /\
            (
              (
                0 <_ ( H ` A )
                /\
                (
                  ( G ` e )
                  +
                  ( H ` ( NTP4VCRight B c ) )
                )
                <
                ( H ` A )
              )
              /\
              (
                A. q e. C A. x e. E
                  (
                    (
                      (
                        P ` <. q , x >.
                      )
                      =
                      (
                        P
                        `
                        <. ( NTP4VCRight B c ) , e >.
                      )
                      /\
                      ( NTP4VCRedex x )
                    )
                    ->
                    (
                      (
                        P ` <. q , x >.
                      )
                      =
                      (
                        P ` <. A , ( NTP4VCCte B ) >.
                      )
                      /\
                      ( NTP4VCRedex x )
                    )
                  )
                /\
                (
                  (
                    ( NTP4VCEmptyContext ( NTP4VCRight B c ) )
                    /\
                    ( NTP4VCValue e )
                  )
                  ->
                  ( NTP4VCEmptyContext A )
                )
              )
            )
          )
        \/
        E. w e. ZZ E. c e. C
          (
            A = ( NTP4VCRight w c )
            /\
            (
              (
                P
                `
                <.
                  c ,
                  (
                    NTP4VCSub
                      ( NTP4VCCte w )
                      ( NTP4VCCte B )
                  )
                >.
              )
              =
              (
                P ` <. A , ( NTP4VCCte B ) >.
              )
              /\
              (
                NTP4VCRedex
                  (
                    NTP4VCSub
                      ( NTP4VCCte w )
                      ( NTP4VCCte B )
                  )
              )
            )
          )
      )
    ) $.
$}
