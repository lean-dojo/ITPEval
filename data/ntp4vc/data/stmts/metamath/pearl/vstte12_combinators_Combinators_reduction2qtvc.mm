$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vstte12_combinators_Combinators_reduction2qtvc: the VSTTE 2012
  call-by-value S-K combinator verification condition for reducing a finite
  term containing only K combinators inside a valid evaluation context. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  T and C are exactly the source inductive carriers of finite combinator terms
  and evaluation contexts. Their tagged constructors are injective and
  disjoint within each carrier; closure, exhaustiveness, and structural
  induction exclude missing constructor trees, extraneous values, and
  non-well-founded constructor objects.

  V, I, and O are respectively the source predicates is_value, is_context,
  and only_K, characterized by their complete constructor equations. F and G
  are the complete recursive functions subst and subst_c. R is exactly the
  one-step call-by-value K/S reduction relation. NTP4VCRTC is its least
  reflexive relation closed under appending one R-step, which is
  definitionally equivalent to the source relTR inductive relation.

  The final assertion keeps the source parameters t and c and hypotheses
  only_K t and is_context c explicit. Source pattern matches are expanded into
  disjoint constructor cases, while all witnesses introduced by matches and
  recursive-call postconditions retain their original internal quantifier
  scopes. The final $a declaration is Metamath's native unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCS NTP4VCK NTP4VCApp
  NTP4VCHole NTP4VCLeft NTP4VCRight
  NTP4VCRTC
$.

ntp4vc-s-syntax $a class NTP4VCS $.
ntp4vc-k-syntax $a class NTP4VCK $.
ntp4vc-app-syntax $a class ( NTP4VCApp A B ) $.

ntp4vc-hole-syntax $a class NTP4VCHole $.
ntp4vc-left-syntax $a class ( NTP4VCLeft A B ) $.
ntp4vc-right-syntax $a class ( NTP4VCRight A B ) $.

ntp4vc-rtc-syntax $a wff ( NTP4VCRTC A B C D ) $.

ntp4vc-s-definition $a |-
  NTP4VCS = <. 0 , (/) >. $.

ntp4vc-k-definition $a |-
  NTP4VCK = <. 1 , (/) >. $.

ntp4vc-app-definition $a |- (
  NTP4VCApp A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-hole-definition $a |-
  NTP4VCHole = <. 0 , (/) >. $.

ntp4vc-left-definition $a |- (
  NTP4VCLeft A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-right-definition $a |- (
  NTP4VCRight A B
) = <. 2 , <. A , B >. >. $.

${
  $d h x y z A B C D $.

  $(
    Least reflexive relation on B closed under appending an A-step.
    This is the source inductive reflexive-transitive closure relTR.
  $)
  ntp4vc-rtc-definition $a |- (
    ( NTP4VCRTC A B C D )
    <->
    A. h e. ~P ( B X. B )
      (
        (
          A. x e. B
            <. x , x >. e. h
          /\
          A. x e. B A. y e. B A. z e. B
            (
              (
                <. x , y >. e. h
                /\
                <. y , z >. e. A
              )
              ->
              <. x , z >. e. h
            )
        )
        ->
        <. C , D >. e. h
      )
  ) $.
$}

${
  $d a b c d e f g h i j k l m n o p q r s t u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite inductive carrier of S-K application terms. $)
  ntp4vc-term-s-closure $e |- NTP4VCS e. T $.

  ntp4vc-term-k-closure $e |- NTP4VCK e. T $.

  ntp4vc-term-app-closure $e |- A. x e. T A. y e. T
    ( NTP4VCApp x y ) e. T $.

  ntp4vc-term-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCS
      \/
      (
        t = NTP4VCK
        \/
        E. x e. T E. y e. T
          t = ( NTP4VCApp x y )
      )
    ) $.

  ntp4vc-term-structural-induction $e |- A. q e. ~P T
    (
      (
        NTP4VCS e. q
        /\
        (
          NTP4VCK e. q
          /\
          A. x e. T A. y e. T
            (
              (
                x e. q
                /\
                y e. q
              )
              ->
              ( NTP4VCApp x y ) e. q
            )
        )
      )
      ->
      q = T
    ) $.

  $( Exact finite inductive carrier of evaluation contexts. $)
  ntp4vc-context-hole-closure $e |- NTP4VCHole e. C $.

  ntp4vc-context-left-closure $e |- A. c e. C A. t e. T
    ( NTP4VCLeft c t ) e. C $.

  ntp4vc-context-right-closure $e |- A. t e. T A. c e. C
    ( NTP4VCRight t c ) e. C $.

  ntp4vc-context-constructor-exhaustive $e |- A. q e. C
    (
      q = NTP4VCHole
      \/
      (
        E. c e. C E. t e. T
          q = ( NTP4VCLeft c t )
        \/
        E. t e. T E. c e. C
          q = ( NTP4VCRight t c )
      )
    ) $.

  ntp4vc-context-structural-induction $e |- A. q e. ~P C
    (
      (
        NTP4VCHole e. q
        /\
        (
          A. c e. C A. t e. T
            (
              c e. q
              ->
              ( NTP4VCLeft c t ) e. q
            )
          /\
          A. t e. T A. c e. C
            (
              c e. q
              ->
              ( NTP4VCRight t c ) e. q
            )
        )
      )
      ->
      q = C
    ) $.

  $( Complete constructor equations for is_value. $)
  ntp4vc-values-subset $e |- V e. ~P T $.

  ntp4vc-value-s $e |- NTP4VCS e. V $.

  ntp4vc-value-k $e |- NTP4VCK e. V $.

  ntp4vc-value-app $e |- A. x e. T A. y e. T
    (
      ( NTP4VCApp x y ) e. V
      <->
      (
        (
          (
            x = NTP4VCK
            \/
            x = NTP4VCS
          )
          /\
          y e. V
        )
        \/
        E. z e. T
          (
            x = ( NTP4VCApp NTP4VCS z )
            /\
            (
              z e. V
              /\
              y e. V
            )
          )
      )
    ) $.

  $( Complete constructor equations for is_context. $)
  ntp4vc-valid-contexts-subset $e |- I e. ~P C $.

  ntp4vc-context-hole-valid $e |- NTP4VCHole e. I $.

  ntp4vc-context-left-valid $e |- A. c e. C A. t e. T
    (
      ( NTP4VCLeft c t ) e. I
      <->
      c e. I
    ) $.

  ntp4vc-context-right-valid $e |- A. t e. T A. c e. C
    (
      ( NTP4VCRight t c ) e. I
      <->
      (
        t e. V
        /\
        c e. I
      )
    ) $.

  $( Complete recursive definition of context substitution subst. $)
  ntp4vc-subst-function $e |- F e. ( T ^m ( C X. T ) ) $.

  ntp4vc-subst-hole $e |- A. t e. T
    (
      F ` <. NTP4VCHole , t >.
    )
    =
    t $.

  ntp4vc-subst-left $e |- A. c e. C A. y e. T A. t e. T
    (
      F ` <. ( NTP4VCLeft c y ) , t >.
    )
    =
    (
      NTP4VCApp
        ( F ` <. c , t >. )
        y
    ) $.

  ntp4vc-subst-right $e |- A. x e. T A. c e. C A. t e. T
    (
      F ` <. ( NTP4VCRight x c ) , t >.
    )
    =
    (
      NTP4VCApp
        x
        ( F ` <. c , t >. )
    ) $.

  $( Complete recursive definition of context composition subst_c. $)
  ntp4vc-subst-c-function $e |- G e. ( C ^m ( C X. C ) ) $.

  ntp4vc-subst-c-hole $e |- A. c e. C
    (
      G ` <. NTP4VCHole , c >.
    )
    =
    c $.

  ntp4vc-subst-c-left $e |- A. c e. C A. t e. T A. d e. C
    (
      G ` <. ( NTP4VCLeft c t ) , d >.
    )
    =
    (
      NTP4VCLeft
        ( G ` <. c , d >. )
        t
    ) $.

  ntp4vc-subst-c-right $e |- A. t e. T A. c e. C A. d e. C
    (
      G ` <. ( NTP4VCRight t c ) , d >.
    )
    =
    (
      NTP4VCRight
        t
        ( G ` <. c , d >. )
    ) $.

  $( Complete constructor equations for the inductive predicate only_K. $)
  ntp4vc-only-k-subset $e |- O e. ~P T $.

  ntp4vc-only-k-s $e |- -. NTP4VCS e. O $.

  ntp4vc-only-k-k $e |- NTP4VCK e. O $.

  ntp4vc-only-k-app $e |- A. x e. T A. y e. T
    (
      ( NTP4VCApp x y ) e. O
      <->
      (
        x e. O
        /\
        y e. O
      )
    ) $.

  $( Exact one-step call-by-value reduction relation. $)
  ntp4vc-step-relation-subset $e |- R e. ~P ( T X. T ) $.

  ntp4vc-step-relation-definition $e |- A. x e. T A. y e. T
    (
      <. x , y >. e. R
      <->
      (
        E. c e. C E. u e. T E. v e. T
          (
            (
              c e. I
              /\
              (
                u e. V
                /\
                v e. V
              )
            )
            /\
            (
              x
              =
              (
                F
                `
                <.
                  c ,
                  (
                    NTP4VCApp
                      ( NTP4VCApp NTP4VCK u )
                      v
                  )
                >.
              )
              /\
              y = ( F ` <. c , u >. )
            )
          )
        \/
        E. c e. C E. u e. T E. v e. T E. w e. T
          (
            (
              c e. I
              /\
              (
                u e. V
                /\
                (
                  v e. V
                  /\
                  w e. V
                )
              )
            )
            /\
            (
              x
              =
              (
                F
                `
                <.
                  c ,
                  (
                    NTP4VCApp
                      (
                        NTP4VCApp
                          ( NTP4VCApp NTP4VCS u )
                          v
                      )
                      w
                  )
                >.
              )
              /\
              y
              =
              (
                F
                `
                <.
                  c ,
                  (
                    NTP4VCApp
                      ( NTP4VCApp u w )
                      ( NTP4VCApp v w )
                  )
                >.
              )
            )
          )
      )
    ) $.

  $( Source theorem parameters t and c, followed by fact0 and fact1. $)
  ntp4vc-t-term $e |- A e. T $.

  ntp4vc-c-context $e |- B e. C $.

  ntp4vc-fact0 $e |- A e. O $.

  ntp4vc-fact1 $e |- B e. I $.

  ntp4vc-pearl-vstte12-combinators-reduction2-vc $a |- (
    (
      A = NTP4VCK
      \/
      E. x e. T E. y e. T
        (
          A = ( NTP4VCApp x y )
          /\
          (
            (
              (
                B e. I
                /\
                ( NTP4VCLeft NTP4VCHole y ) e. I
              )
              ->
              (
                G
                `
                <.
                  B ,
                  ( NTP4VCLeft NTP4VCHole y )
                >.
              )
              e. I
            )
            ->
            (
              (
                (
                  (
                    x = x
                    \/
                    y = x
                  )
                  /\
                  x e. O
                )
                /\
                (
                  G
                  `
                  <.
                    B ,
                    ( NTP4VCLeft NTP4VCHole y )
                  >.
                )
                e. I
              )
              /\
              A. z e. T
                (
                  (
                    (
                      z e. O
                      /\
                      z e. V
                    )
                    /\
                    (
                      NTP4VCRTC
                        R
                        T
                        (
                          F
                          `
                          <.
                            (
                              G
                              `
                              <.
                                B ,
                                ( NTP4VCLeft NTP4VCHole y )
                              >.
                            ) ,
                            x
                          >.
                        )
                        (
                          F
                          `
                          <.
                            (
                              G
                              `
                              <.
                                B ,
                                ( NTP4VCLeft NTP4VCHole y )
                              >.
                            ) ,
                            z
                          >.
                        )
                    )
                  )
                  ->
                  (
                    (
                      (
                        B e. I
                        /\
                        ( NTP4VCRight z NTP4VCHole ) e. I
                      )
                      ->
                      (
                        G
                        `
                        <.
                          B ,
                          ( NTP4VCRight z NTP4VCHole )
                        >.
                      )
                      e. I
                    )
                    ->
                    (
                      (
                        (
                          (
                            x = y
                            \/
                            y = y
                          )
                          /\
                          y e. O
                        )
                        /\
                        (
                          G
                          `
                          <.
                            B ,
                            ( NTP4VCRight z NTP4VCHole )
                          >.
                        )
                        e. I
                      )
                      /\
                      A. w e. T
                        (
                          (
                            (
                              w e. O
                              /\
                              w e. V
                            )
                            /\
                            (
                              NTP4VCRTC
                                R
                                T
                                (
                                  F
                                  `
                                  <.
                                    (
                                      G
                                      `
                                      <.
                                        B ,
                                        (
                                          NTP4VCRight
                                            z
                                            NTP4VCHole
                                        )
                                      >.
                                    ) ,
                                    y
                                  >.
                                )
                                (
                                  F
                                  `
                                  <.
                                    (
                                      G
                                      `
                                      <.
                                        B ,
                                        (
                                          NTP4VCRight
                                            z
                                            NTP4VCHole
                                        )
                                      >.
                                    ) ,
                                    w
                                  >.
                                )
                            )
                          )
                          ->
                          (
                            z = NTP4VCK
                            \/
                            E. u e. T
                              z = ( NTP4VCApp NTP4VCK u )
                          )
                        )
                    )
                  )
                )
            )
          )
        )
    )
    /\
    A. r e. T
      (
        (
          (
            A = NTP4VCK
            /\
            r = NTP4VCK
          )
          \/
          E. x e. T E. y e. T
            (
              A = ( NTP4VCApp x y )
              /\
              (
                (
                  (
                    B e. I
                    /\
                    ( NTP4VCLeft NTP4VCHole y ) e. I
                  )
                  ->
                  (
                    G
                    `
                    <.
                      B ,
                      ( NTP4VCLeft NTP4VCHole y )
                    >.
                  )
                  e. I
                )
                /\
                E. z e. T
                  (
                    (
                      (
                        z e. O
                        /\
                        z e. V
                      )
                      /\
                      (
                        NTP4VCRTC
                          R
                          T
                          (
                            F
                            `
                            <.
                              (
                                G
                                `
                                <.
                                  B ,
                                  ( NTP4VCLeft NTP4VCHole y )
                                >.
                              ) ,
                              x
                            >.
                          )
                          (
                            F
                            `
                            <.
                              (
                                G
                                `
                                <.
                                  B ,
                                  ( NTP4VCLeft NTP4VCHole y )
                                >.
                              ) ,
                              z
                            >.
                          )
                      )
                    )
                    /\
                    (
                      (
                        (
                          B e. I
                          /\
                          ( NTP4VCRight z NTP4VCHole ) e. I
                        )
                        ->
                        (
                          G
                          `
                          <.
                            B ,
                            ( NTP4VCRight z NTP4VCHole )
                          >.
                        )
                        e. I
                      )
                      /\
                      E. w e. T
                        (
                          (
                            (
                              w e. O
                              /\
                              w e. V
                            )
                            /\
                            (
                              NTP4VCRTC
                                R
                                T
                                (
                                  F
                                  `
                                  <.
                                    (
                                      G
                                      `
                                      <.
                                        B ,
                                        (
                                          NTP4VCRight
                                            z
                                            NTP4VCHole
                                        )
                                      >.
                                    ) ,
                                    y
                                  >.
                                )
                                (
                                  F
                                  `
                                  <.
                                    (
                                      G
                                      `
                                      <.
                                        B ,
                                        (
                                          NTP4VCRight
                                            z
                                            NTP4VCHole
                                        )
                                      >.
                                    ) ,
                                    w
                                  >.
                                )
                            )
                          )
                          /\
                          (
                            (
                              z = NTP4VCK
                              /\
                              r = ( NTP4VCApp z w )
                            )
                            \/
                            E. u e. T
                              (
                                z = ( NTP4VCApp NTP4VCK u )
                                /\
                                r = u
                              )
                          )
                        )
                    )
                  )
              )
            )
        )
        ->
        (
          (
            r e. O
            /\
            r e. V
          )
          /\
          (
            NTP4VCRTC
              R
              T
              ( F ` <. B , A >. )
              ( F ` <. B , r >. )
          )
        )
      )
  ) $.
$}
