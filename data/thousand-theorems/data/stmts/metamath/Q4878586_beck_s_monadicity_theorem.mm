$(
  Statement-only formalization of Thousand Theorems corpus artifact Q4878586
  (thousand-theorems__metamath__Q4878586), "Beck's monadicity theorem": a
  right adjoint that creates coequalizers of every pair whose image under it
  has a split coequalizer is monadic. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  C and D are arbitrary SetMM categories, and F and G are native SetMM
  functors. Q4878586Adjunction expands unit and counit naturality and both
  triangle identities. Q4878586SplitCoequalizer and Q4878586Coequalizer state
  the usual split and universal properties without bounding any carrier.

  Q4878586CreatesGSplitCoequalizers says that every displayed split
  coequalizer of the image of a parallel pair lifts to a coequalizer in D,
  with its image identified with the displayed coequalizer by an isomorphism,
  and that G reflects the coequalizer universal property from every cofork on
  such a pair. These lifting and reflection clauses are the standard creation
  property specialized to G-split parallel pairs.

  Q4878586Algebra is an Eilenberg-Moore algebra for the monad induced by an
  adjunction. Q4878586ComparisonEquivalence expands full faithfulness and
  essential surjectivity of the comparison functor. Thus
  Q4878586MonadicRightAdjoint is definitionally the existence of a left
  adjoint whose comparison functor is an equivalence.

  Every declaration before the final assertion is syntax or a bidirectional
  definition. The final $a assertion is the single unproved corpus statement;
  this database contains no $p proof statement.
$)

$c Q4878586Obj Q4878586Map Q4878586Comp Q4878586Id $.
$c Q4878586Coequalizer Q4878586SplitCoequalizer
   Q4878586CreatesGSplitCoequalizers $.
$c Q4878586Adjunction Q4878586Algebra Q4878586AlgebraHom
   Q4878586ComparisonHom Q4878586ComparisonEquivalence
   Q4878586MonadicRightAdjoint $.

q4878586-obj-syntax $a class ( Q4878586Obj G X ) $.
q4878586-map-syntax $a class ( Q4878586Map G X Y f ) $.
q4878586-comp-syntax $a class ( Q4878586Comp C W X Y g f ) $.
q4878586-id-syntax $a class ( Q4878586Id C X ) $.

q4878586-coequalizer-syntax $a wff
  ( Q4878586Coequalizer C A B f g Q q ) $.
q4878586-split-coequalizer-syntax $a wff
  ( Q4878586SplitCoequalizer C A B f g Q q s t ) $.
q4878586-creates-syntax $a wff
  ( Q4878586CreatesGSplitCoequalizers C D G ) $.
q4878586-adjunction-syntax $a wff
  ( Q4878586Adjunction C D F G U E ) $.
q4878586-algebra-syntax $a wff
  ( Q4878586Algebra C D F G U E X a ) $.
q4878586-algebra-hom-syntax $a wff
  ( Q4878586AlgebraHom C D F G U E X a Y b h ) $.
q4878586-comparison-hom-syntax $a wff
  ( Q4878586ComparisonHom C D F G U E X Y h ) $.
q4878586-comparison-equivalence-syntax $a wff
  ( Q4878586ComparisonEquivalence C D F G U E ) $.
q4878586-monadic-right-adjoint-syntax $a wff
  ( Q4878586MonadicRightAdjoint C D G ) $.

q4878586-obj-definition $a |- (
  Q4878586Obj G X
) = ( ( 1st ` G ) ` X ) $.

q4878586-map-definition $a |- (
  Q4878586Map G X Y f
) = ( ( X ( 2nd ` G ) Y ) ` f ) $.

q4878586-comp-definition $a |- (
  Q4878586Comp C W X Y g f
) = ( g ( <. W , X >. ( comp ` C ) Y ) f ) $.

q4878586-id-definition $a |- (
  Q4878586Id C X
) = ( ( Id ` C ) ` X ) $.

${
  $d A B C Q X f g h q u v $.

  q4878586-coequalizer-definition $a |- (
    Q4878586Coequalizer C A B f g Q q
  ) <->
  (
    (
      C e. Cat
      /\
      (
        A e. ( Base ` C )
        /\
        (
          B e. ( Base ` C )
          /\
          Q e. ( Base ` C )
        )
      )
    )
    /\
    (
      (
        f e. ( A ( Hom ` C ) B )
        /\
        (
          g e. ( A ( Hom ` C ) B )
          /\
          q e. ( B ( Hom ` C ) Q )
        )
      )
      /\
      (
        (
          Q4878586Comp C A B Q q f
        ) = (
          Q4878586Comp C A B Q q g
        )
        /\
        A. X e. ( Base ` C )
          A. h e. ( B ( Hom ` C ) X )
            (
              (
                Q4878586Comp C A B X h f
              ) = (
                Q4878586Comp C A B X h g
              )
              ->
              E. u e. ( Q ( Hom ` C ) X )
                (
                  (
                    Q4878586Comp C B Q X u q
                  ) = h
                  /\
                  A. v e. ( Q ( Hom ` C ) X )
                    (
                      (
                        Q4878586Comp C B Q X v q
                      ) = h
                      ->
                      v = u
                    )
                )
            )
      )
    )
  ) $.
$}

${
  $d A B C Q f g q s t $.

  q4878586-split-coequalizer-definition $a |- (
    Q4878586SplitCoequalizer C A B f g Q q s t
  ) <->
  (
    (
      C e. Cat
      /\
      (
        A e. ( Base ` C )
        /\
        (
          B e. ( Base ` C )
          /\
          Q e. ( Base ` C )
        )
      )
    )
    /\
    (
      (
        f e. ( A ( Hom ` C ) B )
        /\
        (
          g e. ( A ( Hom ` C ) B )
          /\
          (
            q e. ( B ( Hom ` C ) Q )
            /\
            (
              s e. ( Q ( Hom ` C ) B )
              /\
              t e. ( B ( Hom ` C ) A )
            )
          )
        )
      )
      /\
      (
        (
          Q4878586Comp C A B Q q f
        ) = (
          Q4878586Comp C A B Q q g
        )
        /\
        (
          (
            Q4878586Comp C Q B Q q s
          ) = (
            Q4878586Id C Q
          )
          /\
          (
            (
              Q4878586Comp C B A B g t
            ) = (
              Q4878586Id C B
            )
            /\
            (
              Q4878586Comp C B A B f t
            ) = (
              Q4878586Comp C B Q B s q
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d A B C D G Q R X Y f g i j q r s t $.

  q4878586-creates-definition $a |- (
    Q4878586CreatesGSplitCoequalizers C D G
  ) <->
  (
    (
      C e. Cat
      /\
      (
        D e. Cat
        /\
        G e. ( D Func C )
      )
    )
    /\
    (
      A. A e. ( Base ` D )
        A. B e. ( Base ` D )
          A. f e. ( A ( Hom ` D ) B )
            A. g e. ( A ( Hom ` D ) B )
              A. Q e. ( Base ` C )
                A. q e. (
                  ( Q4878586Obj G B ) ( Hom ` C ) Q
                )
                  A. s e. (
                    Q ( Hom ` C ) ( Q4878586Obj G B )
                  )
                    A. t e. (
                      ( Q4878586Obj G B )
                        ( Hom ` C )
                      ( Q4878586Obj G A )
                    )
                      (
                        (
                          Q4878586SplitCoequalizer C
                            ( Q4878586Obj G A )
                            ( Q4878586Obj G B )
                            ( Q4878586Map G A B f )
                            ( Q4878586Map G A B g )
                            Q q s t
                        )
                        ->
                        E. R e. ( Base ` D )
                          E. r e. ( B ( Hom ` D ) R )
                            E. i e. (
                              ( Q4878586Obj G R ) ( Hom ` C ) Q
                            )
                              E. j e. (
                                Q ( Hom ` C ) ( Q4878586Obj G R )
                              )
                                (
                                  Q4878586Coequalizer D
                                    A B f g R r
                                  /\
                                  (
                                    (
                                      Q4878586Comp C
                                        ( Q4878586Obj G R )
                                        Q
                                        ( Q4878586Obj G R )
                                        j i
                                    ) = (
                                      Q4878586Id C
                                        ( Q4878586Obj G R )
                                    )
                                    /\
                                    (
                                      (
                                        Q4878586Comp C
                                          Q
                                          ( Q4878586Obj G R )
                                          Q
                                          i j
                                      ) = (
                                        Q4878586Id C Q
                                      )
                                      /\
                                      (
                                        Q4878586Comp C
                                          ( Q4878586Obj G B )
                                          ( Q4878586Obj G R )
                                          Q
                                          i
                                          ( Q4878586Map G B R r )
                                      ) = q
                                    )
                                  )
                                )
                      )
      /\
      A. A e. ( Base ` D )
        A. B e. ( Base ` D )
          A. f e. ( A ( Hom ` D ) B )
            A. g e. ( A ( Hom ` D ) B )
              A. R e. ( Base ` D )
                A. r e. ( B ( Hom ` D ) R )
                  (
                    (
                      (
                        E. Q e. ( Base ` C )
                          E. q e. (
                            ( Q4878586Obj G B ) ( Hom ` C ) Q
                          )
                            E. s e. (
                              Q ( Hom ` C ) ( Q4878586Obj G B )
                            )
                              E. t e. (
                                ( Q4878586Obj G B )
                                  ( Hom ` C )
                                ( Q4878586Obj G A )
                              )
                                (
                                  Q4878586SplitCoequalizer C
                                    ( Q4878586Obj G A )
                                    ( Q4878586Obj G B )
                                    ( Q4878586Map G A B f )
                                    ( Q4878586Map G A B g )
                                    Q q s t
                                )
                        /\
                        (
                          Q4878586Comp D A B R r f
                        ) = (
                          Q4878586Comp D A B R r g
                        )
                      )
                      /\
                      (
                        Q4878586Coequalizer C
                          ( Q4878586Obj G A )
                          ( Q4878586Obj G B )
                          ( Q4878586Map G A B f )
                          ( Q4878586Map G A B g )
                          ( Q4878586Obj G R )
                          ( Q4878586Map G B R r )
                      )
                    )
                    ->
                    Q4878586Coequalizer D A B f g R r
                  )
    )
  ) $.
$}

${
  $d A B C D E F G U X Y f $.

  q4878586-adjunction-definition $a |- (
    Q4878586Adjunction C D F G U E
  ) <->
  (
    (
      C e. Cat
      /\
      (
        D e. Cat
        /\
        (
          F e. ( C Func D )
          /\
          G e. ( D Func C )
        )
      )
    )
    /\
    (
      (
        U e. X_ X e. ( Base ` C )
          (
            X ( Hom ` C )
            ( Q4878586Obj G ( Q4878586Obj F X ) )
          )
        /\
        E e. X_ X e. ( Base ` D )
          (
            ( Q4878586Obj F ( Q4878586Obj G X ) )
              ( Hom ` D ) X
          )
      )
      /\
      (
        A. A e. ( Base ` C )
          A. B e. ( Base ` C )
            A. f e. ( A ( Hom ` C ) B )
              (
                Q4878586Comp C
                  A
                  ( Q4878586Obj G ( Q4878586Obj F A ) )
                  ( Q4878586Obj G ( Q4878586Obj F B ) )
                  ( Q4878586Map G
                    ( Q4878586Obj F A )
                    ( Q4878586Obj F B )
                    ( Q4878586Map F A B f )
                  )
                  ( U ` A )
              ) = (
                Q4878586Comp C
                  A
                  B
                  ( Q4878586Obj G ( Q4878586Obj F B ) )
                  ( U ` B )
                  f
              )
        /\
        (
          A. A e. ( Base ` D )
            A. B e. ( Base ` D )
              A. f e. ( A ( Hom ` D ) B )
                (
                  Q4878586Comp D
                    ( Q4878586Obj F ( Q4878586Obj G A ) )
                    A
                    B
                    f
                    ( E ` A )
                ) = (
                  Q4878586Comp D
                    ( Q4878586Obj F ( Q4878586Obj G A ) )
                    ( Q4878586Obj F ( Q4878586Obj G B ) )
                    B
                    ( E ` B )
                    ( Q4878586Map F
                      ( Q4878586Obj G A )
                      ( Q4878586Obj G B )
                      ( Q4878586Map G A B f )
                    )
                )
          /\
          (
            A. X e. ( Base ` C )
              (
                Q4878586Comp D
                  ( Q4878586Obj F X )
                  ( Q4878586Obj F
                    ( Q4878586Obj G ( Q4878586Obj F X ) )
                  )
                  ( Q4878586Obj F X )
                  ( E ` ( Q4878586Obj F X ) )
                  ( Q4878586Map F
                    X
                    ( Q4878586Obj G ( Q4878586Obj F X ) )
                    ( U ` X )
                  )
              ) = (
                Q4878586Id D ( Q4878586Obj F X )
              )
            /\
            A. X e. ( Base ` D )
              (
                Q4878586Comp C
                  ( Q4878586Obj G X )
                  ( Q4878586Obj G
                    ( Q4878586Obj F ( Q4878586Obj G X ) )
                  )
                  ( Q4878586Obj G X )
                  ( Q4878586Map G
                    ( Q4878586Obj F ( Q4878586Obj G X ) )
                    X
                    ( E ` X )
                  )
                  ( U ` ( Q4878586Obj G X ) )
              ) = (
                Q4878586Id C ( Q4878586Obj G X )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d C D E F G U X a $.

  q4878586-algebra-definition $a |- (
    Q4878586Algebra C D F G U E X a
  ) <->
  (
    (
      Q4878586Adjunction C D F G U E
      /\
      (
        X e. ( Base ` C )
        /\
        a e. (
          ( Q4878586Obj G ( Q4878586Obj F X ) )
            ( Hom ` C ) X
        )
      )
    )
    /\
    (
      (
        Q4878586Comp C
          X
          ( Q4878586Obj G ( Q4878586Obj F X ) )
          X
          a
          ( U ` X )
      ) = (
        Q4878586Id C X
      )
      /\
      (
        Q4878586Comp C
          ( Q4878586Obj G
            ( Q4878586Obj F
              ( Q4878586Obj G ( Q4878586Obj F X ) )
            )
          )
          ( Q4878586Obj G ( Q4878586Obj F X ) )
          X
          a
          ( Q4878586Map G
            ( Q4878586Obj F
              ( Q4878586Obj G ( Q4878586Obj F X ) )
            )
            ( Q4878586Obj F X )
            ( Q4878586Map F
              ( Q4878586Obj G ( Q4878586Obj F X ) )
              X
              a
            )
          )
      ) = (
        Q4878586Comp C
          ( Q4878586Obj G
            ( Q4878586Obj F
              ( Q4878586Obj G ( Q4878586Obj F X ) )
            )
          )
          ( Q4878586Obj G ( Q4878586Obj F X ) )
          X
          a
          ( Q4878586Map G
            ( Q4878586Obj F
              ( Q4878586Obj G ( Q4878586Obj F X ) )
            )
            ( Q4878586Obj F X )
            ( E ` ( Q4878586Obj F X ) )
          )
      )
    )
  ) $.
$}

${
  $d C D E F G U X Y a b h $.

  q4878586-algebra-hom-definition $a |- (
    Q4878586AlgebraHom C D F G U E X a Y b h
  ) <->
  (
    (
      Q4878586Algebra C D F G U E X a
      /\
      (
        Q4878586Algebra C D F G U E Y b
        /\
        h e. ( X ( Hom ` C ) Y )
      )
    )
    /\
    (
      Q4878586Comp C
        ( Q4878586Obj G ( Q4878586Obj F X ) )
        X
        Y
        h
        a
    ) = (
      Q4878586Comp C
        ( Q4878586Obj G ( Q4878586Obj F X ) )
        ( Q4878586Obj G ( Q4878586Obj F Y ) )
        Y
        b
        ( Q4878586Map G
          ( Q4878586Obj F X )
          ( Q4878586Obj F Y )
          ( Q4878586Map F X Y h )
        )
    )
  ) $.
$}

${
  $d C D E F G U X Y h $.

  q4878586-comparison-hom-definition $a |- (
    Q4878586ComparisonHom C D F G U E X Y h
  ) <->
  (
    h e. (
      ( Q4878586Obj G X )
        ( Hom ` C )
      ( Q4878586Obj G Y )
    )
    /\
    (
      Q4878586Comp C
        ( Q4878586Obj G
          ( Q4878586Obj F ( Q4878586Obj G X ) )
        )
        ( Q4878586Obj G X )
        ( Q4878586Obj G Y )
        h
        ( Q4878586Map G
          ( Q4878586Obj F ( Q4878586Obj G X ) )
          X
          ( E ` X )
        )
    ) = (
      Q4878586Comp C
        ( Q4878586Obj G
          ( Q4878586Obj F ( Q4878586Obj G X ) )
        )
        ( Q4878586Obj G
          ( Q4878586Obj F ( Q4878586Obj G Y ) )
        )
        ( Q4878586Obj G Y )
        ( Q4878586Map G
          ( Q4878586Obj F ( Q4878586Obj G Y ) )
          Y
          ( E ` Y )
        )
        ( Q4878586Map G
          ( Q4878586Obj F ( Q4878586Obj G X ) )
          ( Q4878586Obj F ( Q4878586Obj G Y ) )
          ( Q4878586Map F
            ( Q4878586Obj G X )
            ( Q4878586Obj G Y )
            h
          )
        )
    )
  ) $.
$}

${
  $d C D E F G U X Y Z a f g h i j k $.

  q4878586-comparison-equivalence-definition $a |- (
    Q4878586ComparisonEquivalence C D F G U E
  ) <->
  (
    Q4878586Adjunction C D F G U E
    /\
    (
      A. X e. ( Base ` D )
        A. Y e. ( Base ` D )
          A. f e. ( X ( Hom ` D ) Y )
            A. g e. ( X ( Hom ` D ) Y )
              (
                (
                  Q4878586Map G X Y f
                ) = (
                  Q4878586Map G X Y g
                )
                ->
                f = g
              )
      /\
      (
        A. X e. ( Base ` D )
          A. Y e. ( Base ` D )
            A. h e. (
              ( Q4878586Obj G X )
                ( Hom ` C )
              ( Q4878586Obj G Y )
            )
              (
                Q4878586ComparisonHom C D F G U E X Y h
                ->
                E. k e. ( X ( Hom ` D ) Y )
                  (
                    Q4878586Map G X Y k
                  ) = h
              )
        /\
        A. Z e. ( Base ` C )
          A. a e. (
            ( Q4878586Obj G ( Q4878586Obj F Z ) )
              ( Hom ` C ) Z
          )
            (
              Q4878586Algebra C D F G U E Z a
              ->
              E. X e. ( Base ` D )
                E. i e. (
                  Z ( Hom ` C ) ( Q4878586Obj G X )
                )
                  E. j e. (
                    ( Q4878586Obj G X ) ( Hom ` C ) Z
                  )
                    (
                      (
                        Q4878586AlgebraHom C D F G U E
                          Z a
                          ( Q4878586Obj G X )
                          ( Q4878586Map G
                            ( Q4878586Obj F ( Q4878586Obj G X ) )
                            X
                            ( E ` X )
                          )
                          i
                        /\
                        Q4878586AlgebraHom C D F G U E
                          ( Q4878586Obj G X )
                          ( Q4878586Map G
                            ( Q4878586Obj F ( Q4878586Obj G X ) )
                            X
                            ( E ` X )
                          )
                          Z a j
                      )
                      /\
                      (
                        (
                          Q4878586Comp C
                            Z
                            ( Q4878586Obj G X )
                            Z
                            j i
                        ) = (
                          Q4878586Id C Z
                        )
                        /\
                        (
                          Q4878586Comp C
                            ( Q4878586Obj G X )
                            Z
                            ( Q4878586Obj G X )
                            i j
                        ) = (
                          Q4878586Id C ( Q4878586Obj G X )
                        )
                      )
                    )
            )
      )
    )
  ) $.
$}

${
  $d C D E F G U $.

  q4878586-monadic-right-adjoint-definition $a |- (
    Q4878586MonadicRightAdjoint C D G
  ) <->
  (
    E. F E. U E. E
      (
        Q4878586ComparisonEquivalence C D F G U E
      )
  ) $.
$}

${
  $d C D E F G U $.

  thousand-theorems-q4878586-beck-s-monadicity-theorem $a |-
    A. C A. D A. F A. G A. U A. E
      (
        (
          Q4878586Adjunction C D F G U E
          /\
          Q4878586CreatesGSplitCoequalizers C D G
        )
        ->
        Q4878586MonadicRightAdjoint C D G
      )
  $.
$}
