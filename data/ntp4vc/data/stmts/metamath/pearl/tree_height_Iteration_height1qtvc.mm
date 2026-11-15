$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/tree_height_Iteration_height1qtvc
  (ntp4vc__metamath__pearl/tree_height_Iteration_height1qtvc):
  the iterative tree-height verification condition initializes and preserves
  the continuation-machine height invariant, strictly decreases its integer
  size measure on every loop step, and returns the tree height at termination.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source element carrier. T, C, and W are
  exactly the source inductive carriers of finite U-labelled binary trees,
  continuations, and machine states. Their tagged constructors are disjoint
  and injective; closure, exhaustiveness, and structural induction exclude
  missing finite values and extraneous non-well-founded values.

  H and S are the complete recursive source height and tree-size functions.
  E, V, K, and Q are respectively evalk, evalw, sizek, and sizew, with their
  complete recursive equations. NTP4VCMax is integer maximum and
  NTP4VCMeasure is the source variant sizek k + sizew w.

  NTP4VCGuard is exactly the Boolean assignment to the source local o1.
  NTP4VCStep combines the two Argument cases and the two non-Id Result cases
  of the exhaustive source match, retaining both nonnegativity and strict
  variant decrease together with invariant preservation. NTP4VCFinish is the
  Result-only terminal match and its universally quantified extraction
  condition. The proposition-valued source conditional is rendered by its
  two exhaustive Boolean guards. Every source domain and quantifier scope is
  unchanged. The final $a declaration is Metamath's native unproved statement
  encoding; every preceding $a is syntax or a faithful definition, and this
  database contains no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode
  NTP4VCId NTP4VCKleft NTP4VCKright
  NTP4VCArgument NTP4VCResult
  NTP4VCMax NTP4VCMeasure NTP4VCInvariant
  NTP4VCIsResult NTP4VCGuard NTP4VCStep NTP4VCFinish
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.
ntp4vc-id-syntax $a class NTP4VCId $.
ntp4vc-kleft-syntax $a class ( NTP4VCKleft A B ) $.
ntp4vc-kright-syntax $a class ( NTP4VCKright A B ) $.
ntp4vc-argument-syntax $a class ( NTP4VCArgument A ) $.
ntp4vc-result-syntax $a class ( NTP4VCResult A ) $.
ntp4vc-max-syntax $a class ( NTP4VCMax A B ) $.
ntp4vc-measure-syntax $a class ( NTP4VCMeasure A B C D ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F ) $.
ntp4vc-is-result-syntax $a wff ( NTP4VCIsResult A ) $.
ntp4vc-guard-syntax $a wff ( NTP4VCGuard A B C ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G H I J K ) $.
ntp4vc-finish-syntax $a wff ( NTP4VCFinish A B C ) $.

ntp4vc-empty-definition $a |- (
  NTP4VCEmpty
) = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-id-definition $a |- (
  NTP4VCId
) = <. 0 , (/) >. $.

ntp4vc-kleft-definition $a |- (
  NTP4VCKleft A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-kright-definition $a |- (
  NTP4VCKright A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-argument-definition $a |- (
  NTP4VCArgument A
) = <. 0 , A >. $.

ntp4vc-result-definition $a |- (
  NTP4VCResult A
) = <. 1 , A >. $.

ntp4vc-max-definition $a |- (
  NTP4VCMax A B
) = if (
  A <_ B ,
  B ,
  A
) $.

ntp4vc-measure-definition $a |- (
  NTP4VCMeasure A B C D
) = (
  ( A ` C )
  +
  ( B ` D )
) $.

ntp4vc-invariant-definition $a |- (
  ( NTP4VCInvariant A B C D E F )
  <->
  (
    A ` <. E , ( B ` F ) >.
  )
  =
  ( C ` D )
) $.

${
  $d z A $.

  ntp4vc-is-result-definition $a |- (
    ( NTP4VCIsResult A )
    <->
    E. z e. ZZ
      A = ( NTP4VCResult z )
  ) $.
$}

ntp4vc-guard-definition $a |- (
  ( NTP4VCGuard A B C )
  <->
  (
    (
      A = NTP4VCId
      /\
      (
        (
          ( NTP4VCIsResult B )
          /\
          C = 1
        )
        \/
        (
          ( -. ( NTP4VCIsResult B ) )
          /\
          C = 0
        )
      )
    )
    \/
    (
      A =/= NTP4VCId
      /\
      C = 0
    )
  )
) $.

${
  $d h l q r v x
     A B C D E F G H I J K $.

  $(
    A=T, B=U, C=continuation carrier, D=evalk, E=evalw,
    F=height, G=sizek, H=sizew, I=source tree, J=current
    continuation, and K=current machine state.
  $)
  ntp4vc-step-definition $a |- (
    ( NTP4VCStep A B C D E F G H I J K )
    <->
    (
      (
        K = ( NTP4VCArgument NTP4VCEmpty )
        /\
        (
          (
            0 <_ ( NTP4VCMeasure G H J K )
            /\
            (
              NTP4VCMeasure
                G H J ( NTP4VCResult 0 )
            )
            <
            ( NTP4VCMeasure G H J K )
          )
          /\
          (
            NTP4VCInvariant
              D E F I J ( NTP4VCResult 0 )
          )
        )
      )
      \/
      (
        E. l e. A E. x e. B E. r e. A
          (
            K = (
              NTP4VCArgument
                ( NTP4VCNode l x r )
            )
            /\
            (
              (
                0 <_ ( NTP4VCMeasure G H J K )
                /\
                (
                  NTP4VCMeasure
                    G H
                    ( NTP4VCKleft r J )
                    ( NTP4VCArgument l )
                )
                <
                ( NTP4VCMeasure G H J K )
              )
              /\
              (
                NTP4VCInvariant
                  D E F I
                  ( NTP4VCKleft r J )
                  ( NTP4VCArgument l )
              )
            )
          )
      )
      \/
      (
        E. r e. A E. q e. C E. v e. ZZ
          (
            J = ( NTP4VCKleft r q )
            /\
            (
              K = ( NTP4VCResult v )
              /\
              (
                (
                  0 <_ ( NTP4VCMeasure G H J K )
                  /\
                  (
                    NTP4VCMeasure
                      G H
                      ( NTP4VCKright v q )
                      ( NTP4VCArgument r )
                  )
                  <
                  ( NTP4VCMeasure G H J K )
                )
                /\
                (
                  NTP4VCInvariant
                    D E F I
                    ( NTP4VCKright v q )
                    ( NTP4VCArgument r )
                )
              )
            )
          )
      )
      \/
      (
        E. h e. ZZ E. q e. C E. v e. ZZ
          (
            J = ( NTP4VCKright h q )
            /\
            (
              K = ( NTP4VCResult v )
              /\
              (
                (
                  0 <_ ( NTP4VCMeasure G H J K )
                  /\
                  (
                    NTP4VCMeasure
                      G H q
                      (
                        NTP4VCResult
                          (
                            1
                            +
                            ( NTP4VCMax h v )
                          )
                      )
                  )
                  <
                  ( NTP4VCMeasure G H J K )
                )
                /\
                (
                  NTP4VCInvariant
                    D E F I q
                    (
                      NTP4VCResult
                        (
                          1
                          +
                          ( NTP4VCMax h v )
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
  $d r z A B C $.

  ntp4vc-finish-definition $a |- (
    ( NTP4VCFinish A B C )
    <->
    E. r e. ZZ
      (
        C = ( NTP4VCResult r )
        /\
        A. z e. ZZ
          (
            z = r
            ->
            z = ( A ` B )
          )
      )
  ) $.
$}

${
  $d h k l o q r s t u v w x z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Arbitrary inhabited source carrier and exact finite tree datatype. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.

  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. x e. U A. r e. T
    ( NTP4VCNode l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. x e. U E. r e. T
        t = ( NTP4VCNode l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. x e. U A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l x r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Exact finite continuation datatype over trees and integers. $)
  ntp4vc-cont-id-closure $e |- NTP4VCId e. C $.

  ntp4vc-cont-kleft-closure $e |- A. t e. T A. k e. C
    ( NTP4VCKleft t k ) e. C $.

  ntp4vc-cont-kright-closure $e |- A. z e. ZZ A. k e. C
    ( NTP4VCKright z k ) e. C $.

  ntp4vc-cont-constructor-exhaustive $e |- A. k e. C
    (
      k = NTP4VCId
      \/
      E. t e. T E. q e. C
        k = ( NTP4VCKleft t q )
      \/
      E. z e. ZZ E. q e. C
        k = ( NTP4VCKright z q )
    ) $.

  ntp4vc-cont-structural-induction $e |- A. s e. ~P C
    (
      (
        NTP4VCId e. s
        /\
        (
          A. t e. T A. k e. C
            (
              k e. s
              ->
              ( NTP4VCKleft t k ) e. s
            )
          /\
          A. z e. ZZ A. k e. C
            (
              k e. s
              ->
              ( NTP4VCKright z k ) e. s
            )
        )
      )
      ->
      s = C
    ) $.

  $( Exact source what datatype. $)
  ntp4vc-what-argument-closure $e |- A. t e. T
    ( NTP4VCArgument t ) e. W $.

  ntp4vc-what-result-closure $e |- A. z e. ZZ
    ( NTP4VCResult z ) e. W $.

  ntp4vc-what-constructor-exhaustive $e |- A. w e. W
    (
      E. t e. T
        w = ( NTP4VCArgument t )
      \/
      E. z e. ZZ
        w = ( NTP4VCResult z )
    ) $.

  $( Complete recursive definitions of source tree height and size. $)
  ntp4vc-height-function $e |- H e. ( ZZ ^m T ) $.
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.

  ntp4vc-height-empty $e |- (
    H ` NTP4VCEmpty
  ) = 0 $.

  ntp4vc-height-node $e |- A. l e. T A. x e. U A. r e. T
    (
      H ` ( NTP4VCNode l x r )
    )
    =
    (
      1
      +
      (
        NTP4VCMax
          ( H ` l )
          ( H ` r )
      )
    ) $.

  ntp4vc-size-empty $e |- (
    S ` NTP4VCEmpty
  ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. x e. U A. r e. T
    (
      S ` ( NTP4VCNode l x r )
    )
    =
    (
      (
        1
        +
        ( S ` l )
      )
      +
      ( S ` r )
    ) $.

  $( Complete recursive definition of evalk. $)
  ntp4vc-evalk-function $e |- E e.
    (
      ZZ
      ^m
      ( C X. ZZ )
    ) $.

  ntp4vc-evalk-id $e |- A. z e. ZZ
    (
      E ` <. NTP4VCId , z >.
    ) = z $.

  ntp4vc-evalk-kleft $e |- A. t e. T A. k e. C A. z e. ZZ
    (
      E ` <. ( NTP4VCKleft t k ) , z >.
    )
    =
    (
      E `
      <.
        k ,
        (
          1
          +
          (
            NTP4VCMax
              ( H ` t )
              z
          )
        )
      >.
    ) $.

  ntp4vc-evalk-kright $e |- A. h e. ZZ A. k e. C A. z e. ZZ
    (
      E ` <. ( NTP4VCKright h k ) , z >.
    )
    =
    (
      E `
      <.
        k ,
        (
          1
          +
          ( NTP4VCMax h z )
        )
      >.
    ) $.

  $( Complete source definitions of evalw, sizek, and sizew. $)
  ntp4vc-evalw-function $e |- V e. ( ZZ ^m W ) $.

  ntp4vc-evalw-argument $e |- A. t e. T
    (
      V ` ( NTP4VCArgument t )
    ) = ( H ` t ) $.

  ntp4vc-evalw-result $e |- A. z e. ZZ
    (
      V ` ( NTP4VCResult z )
    ) = z $.

  ntp4vc-sizek-function $e |- K e. ( ZZ ^m C ) $.

  ntp4vc-sizek-id $e |- (
    K ` NTP4VCId
  ) = 0 $.

  ntp4vc-sizek-kleft $e |- A. t e. T A. k e. C
    (
      K ` ( NTP4VCKleft t k )
    )
    =
    (
      (
        3
        +
        (
          4
          x.
          ( S ` t )
        )
      )
      +
      ( K ` k )
    ) $.

  ntp4vc-sizek-kright $e |- A. z e. ZZ A. k e. C
    (
      K ` ( NTP4VCKright z k )
    )
    =
    (
      1
      +
      ( K ` k )
    ) $.

  ntp4vc-sizew-function $e |- Q e. ( ZZ ^m W ) $.

  ntp4vc-sizew-argument $e |- A. t e. T
    (
      Q ` ( NTP4VCArgument t )
    )
    =
    (
      1
      +
      (
        4
        x.
        ( S ` t )
      )
    ) $.

  ntp4vc-sizew-result $e |- A. z e. ZZ
    (
      Q ` ( NTP4VCResult z )
    ) = 0 $.

  ntp4vc-pearl-tree-height-iteration-height1-vc $a |-
    A. t e. T
      (
        (
          E `
          <.
            NTP4VCId ,
            ( V ` ( NTP4VCArgument t ) )
          >.
        )
        =
        ( H ` t )
        /\
        A. k e. C A. w e. W
          (
            (
              NTP4VCInvariant
                E V H t k w
            )
            ->
            A. o e. { 0 , 1 }
              (
                (
                  NTP4VCGuard k w o
                )
                ->
                (
                  (
                    o =/= 1
                    /\
                    (
                      NTP4VCStep
                        T U C E V H K Q t k w
                    )
                  )
                  \/
                  (
                    o = 1
                    /\
                    (
                      NTP4VCFinish H t w
                    )
                  )
                )
              )
          )
      ) $.
$}
