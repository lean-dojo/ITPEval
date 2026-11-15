$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/defunctionalization_SemWithError_continue_4qtvc: the error-aware
  defunctionalized continuation verification condition states the recursive
  size obligations for each continuation constructor and preservation of the
  inductively generated continuation-evaluation relation for a nonnegative
  numeric value. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  E, T, and V are exactly the source finite inductive carriers of arithmetic
  expressions, continuations, and error-aware values. Their tagged
  constructors are disjoint and injective; closure, exhaustiveness, and
  structural induction exclude missing constructor trees, extraneous values,
  and non-well-founded constructor objects.

  F is error-aware expression evaluation, G is the expression-size function
  used by the source continuation measure, and H is continuation size. Their
  displayed equations are the complete recursive definitions. R is exactly
  the least ternary relation on T x V x V closed under the four source
  eval_cont introduction rules, including propagation of Underflow.

  The source matches on c are expanded into their three disjoint constructor
  cases, with constructor fields existentially scoped inside each case and
  result universally scoped over V. The proposition-valued conditional in
  the B case is expanded into its equivalent nonnegative and negative order
  branches. The hypothesis that v is nonnegative remains explicit, and all
  source integers range over the full SetMM integer class ZZ. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c
  NTP4VCCte NTP4VCSub
  NTP4VCI NTP4VCA NTP4VCB
  NTP4VCVnum NTP4VCUnderflow
  NTP4VCEval NTP4VCEvalClosed
$.

ntp4vc-cte-syntax $a class ( NTP4VCCte A ) $.
ntp4vc-sub-syntax $a class ( NTP4VCSub A B ) $.

ntp4vc-i-syntax $a class NTP4VCI $.
ntp4vc-a-syntax $a class ( NTP4VCA A B ) $.
ntp4vc-b-syntax $a class ( NTP4VCB A B ) $.

ntp4vc-vnum-syntax $a class ( NTP4VCVnum A ) $.
ntp4vc-underflow-syntax $a class NTP4VCUnderflow $.

ntp4vc-eval-syntax
  $a wff ( NTP4VCEval A B C D ) $.
ntp4vc-eval-closed-syntax
  $a wff ( NTP4VCEvalClosed A B C D E ) $.

ntp4vc-cte-definition $a |- (
  NTP4VCCte A
) = <. 0 , A >. $.

ntp4vc-sub-definition $a |- (
  NTP4VCSub A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-i-definition $a |- NTP4VCI = <. 0 , (/) >. $.

ntp4vc-a-definition $a |- (
  NTP4VCA A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-b-definition $a |- (
  NTP4VCB A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-vnum-definition $a |- (
  NTP4VCVnum A
) = <. 0 , A >. $.

ntp4vc-underflow-definition $a |-
  NTP4VCUnderflow = <. 1 , (/) >. $.

ntp4vc-eval-definition $a |- (
  ( NTP4VCEval A B C D )
  <->
  <. B , <. C , D >. >. e. A
) $.

${
  $d e k r u v w A B C D E $.

  ntp4vc-eval-closed-definition $a |- (
    ( NTP4VCEvalClosed A B C D E )
    <->
    (
      A. k e. C
        (
          NTP4VCEval
            A k NTP4VCUnderflow NTP4VCUnderflow
        )
      /\
      (
        A. v e. ZZ A. k e. C A. e e. B A. r e. D
          (
            (
              NTP4VCEval
                A ( NTP4VCB v k ) ( E ` e ) r
            )
            ->
            (
              NTP4VCEval
                A ( NTP4VCA e k ) ( NTP4VCVnum v ) r
            )
          )
        /\
        (
          A. k e. C A. u e. ZZ A. w e. ZZ A. r e. D
            (
              (
                NTP4VCEval
                  A
                  k
                  if (
                    u <_ w ,
                    ( NTP4VCVnum ( w - u ) ) ,
                    NTP4VCUnderflow
                  )
                  r
              )
              ->
              (
                NTP4VCEval
                  A ( NTP4VCB w k ) ( NTP4VCVnum u ) r
              )
            )
          /\
          A. v e. ZZ
            (
              NTP4VCEval
                A
                NTP4VCI
                ( NTP4VCVnum v )
                ( NTP4VCVnum v )
            )
        )
      )
    )
  ) $.
$}

${
  $d c e k n q r s u v w x y z
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

  $( Exact finite inductive continuation carrier. $)
  ntp4vc-cont-i-closure $e |- NTP4VCI e. T $.

  ntp4vc-cont-a-closure $e |- A. e e. E A. k e. T
    ( NTP4VCA e k ) e. T $.

  ntp4vc-cont-b-closure $e |- A. v e. ZZ A. k e. T
    ( NTP4VCB v k ) e. T $.

  ntp4vc-cont-constructor-exhaustive $e |- A. q e. T
    (
      q = NTP4VCI
      \/
      (
        E. e e. E E. k e. T
          q = ( NTP4VCA e k )
        \/
        E. v e. ZZ E. k e. T
          q = ( NTP4VCB v k )
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
              ( NTP4VCA e k ) e. s
            )
          /\
          A. v e. ZZ A. k e. T
            (
              k e. s
              ->
              ( NTP4VCB v k ) e. s
            )
        )
      )
      ->
      s = T
    ) $.

  $( Exact error-aware value carrier. $)
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

  $( Complete recursive continuation-size definition. $)
  ntp4vc-size-c-function $e |- H e. ( ZZ ^m T ) $.

  ntp4vc-size-c-i $e |- ( H ` NTP4VCI ) = 0 $.

  ntp4vc-size-c-a $e |- A. e e. E A. k e. T
    (
      H ` ( NTP4VCA e k )
    )
    =
    (
      ( 2 + ( G ` e ) )
      +
      ( H ` k )
    ) $.

  ntp4vc-size-c-b $e |- A. v e. ZZ A. k e. T
    (
      H ` ( NTP4VCB v k )
    )
    =
    (
      1
      +
      ( H ` k )
    ) $.

  $( Exact least relation generated by the four eval_cont rules. $)
  ntp4vc-eval-relation-type $e |- R C_
    ( T X. ( V X. V ) ) $.

  ntp4vc-eval-relation-closed $e |-
    ( NTP4VCEvalClosed R E T V F ) $.

  ntp4vc-eval-relation-least $e |- A. q e.
    ~P ( T X. ( V X. V ) )
    (
      ( NTP4VCEvalClosed q E T V F )
      ->
      R C_ q
    ) $.

  $( Source theorem parameters v and c, and fact0 that v is nonnegative. $)
  ntp4vc-v-integer $e |- A e. ZZ $.
  ntp4vc-c-continuation $e |- B e. T $.
  ntp4vc-fact0 $e |- 0 <_ A $.

  ntp4vc-pearl-defunctionalization-semwitherror-continue-4-vc $a |- (
    (
      (
        E. e e. E E. k e. T
          (
            B = ( NTP4VCA e k )
            /\
            (
              0 <_ ( H ` B )
              /\
              (
                (
                  ( H ` ( NTP4VCB A k ) )
                  +
                  ( G ` e )
                )
                <
                ( H ` B )
              )
            )
          )
        \/
        E. w e. ZZ E. k e. T
          (
            B = ( NTP4VCB w k )
            /\
            (
              A <_ w
              ->
              (
                (
                  0 <_ ( H ` B )
                  /\
                  ( H ` k ) < ( H ` B )
                )
                /\
                0 <_ ( w - A )
              )
            )
          )
      )
      \/
      B = NTP4VCI
    )
    /\
    A. r e. V
      (
        (
          (
            E. e e. E E. k e. T
              (
                B = ( NTP4VCA e k )
                /\
                (
                  NTP4VCEval
                    R ( NTP4VCB A k ) ( F ` e ) r
                )
              )
            \/
            E. w e. ZZ E. k e. T
              (
                B = ( NTP4VCB w k )
                /\
                (
                  (
                    A <_ w
                    /\
                    (
                      NTP4VCEval
                        R k ( NTP4VCVnum ( w - A ) ) r
                    )
                  )
                  \/
                  (
                    -. A <_ w
                    /\
                    r = NTP4VCUnderflow
                  )
                )
              )
          )
          \/
          (
            B = NTP4VCI
            /\
            r = ( NTP4VCVnum A )
          )
        )
        ->
        (
          NTP4VCEval
            R B ( NTP4VCVnum A ) r
        )
      )
  ) $.
$}
