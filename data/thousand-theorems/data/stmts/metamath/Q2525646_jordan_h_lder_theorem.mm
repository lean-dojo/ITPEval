$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2525646
  (thousand-theorems__metamath__Q2525646), "Jordan&ndash;H&ouml;lder theorem":
  in an arbitrary Jordan&ndash;H&ouml;lder lattice, any two finite composition series with
  the same least and greatest elements have bijectively matched successive
  factors up to the lattice's factor-isomorphism relation. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  K is a SetMM lattice. M is the maximal-step relation on its carrier, and I
  is the factor-isomorphism relation on pairs of carrier elements.
  Q2525646JHL states exactly the JordanHolderLattice laws used by the Lean
  source: maximal steps are strict, distinct maximal predecessors have join
  equal to their common successor, meets inherit maximality, I is symmetric
  and transitive, and the second isomorphism law holds.

  A composition series is represented by a nonempty SetMM word over the
  lattice carrier whose adjacent entries satisfy M. Its factor indices form
  the finite ordinal 0 ..^ (#s - 1). Q2525646Equivalent internally quantifies
  a bijection between the two factor-index ordinals and requires I-related
  adjacent pairs at corresponding indices.

  The declarations preceding the final assertion are syntax or faithful
  bidirectional definitions. The final $a declaration is the single unproved
  corpus statement; this database contains no $p proof statement.
$)

$c Q2525646JHL Q2525646Series Q2525646Equivalent $.

q2525646-jhl-syntax
  $a wff ( Q2525646JHL K M I ) $.
q2525646-series-syntax
  $a wff ( Q2525646Series K M s ) $.
q2525646-equivalent-syntax
  $a wff ( Q2525646Equivalent I s t ) $.

${
  $d I K M p q r x y z $.

  q2525646-jhl-definition $a |- (
    Q2525646JHL K M I
  ) <->
  (
    K e. Lat
    /\
    (
      M C_ ( ( Base ` K ) X. ( Base ` K ) )
      /\
      (
        I C_ (
          ( ( Base ` K ) X. ( Base ` K ) )
          X.
          ( ( Base ` K ) X. ( Base ` K ) )
        )
        /\
        (
          A. x e. ( Base ` K )
            A. y e. ( Base ` K )
              (
                x M y
                ->
                (
                  x ( le ` K ) y
                  /\
                  x =/= y
                )
              )
          /\
          (
            A. x e. ( Base ` K )
              A. y e. ( Base ` K )
                A. z e. ( Base ` K )
                  (
                    (
                      x M z
                      /\
                      (
                        y M z
                        /\
                        x =/= y
                      )
                    )
                    ->
                    ( x ( join ` K ) y ) = z
                  )
            /\
            (
              A. x e. ( Base ` K )
                A. y e. ( Base ` K )
                  (
                    (
                      x M ( x ( join ` K ) y )
                      /\
                      y M ( x ( join ` K ) y )
                    )
                    ->
                    ( x ( meet ` K ) y ) M x
                  )
              /\
              (
                A. p e. (
                  ( Base ` K ) X. ( Base ` K )
                )
                  A. q e. (
                    ( Base ` K ) X. ( Base ` K )
                  )
                    (
                      p I q
                      ->
                      q I p
                    )
                /\
                (
                  A. p e. (
                    ( Base ` K ) X. ( Base ` K )
                  )
                    A. q e. (
                      ( Base ` K ) X. ( Base ` K )
                    )
                      A. r e. (
                        ( Base ` K ) X. ( Base ` K )
                      )
                        (
                          (
                            p I q
                            /\
                            q I r
                          )
                          ->
                          p I r
                        )
                  /\
                  A. x e. ( Base ` K )
                    A. y e. ( Base ` K )
                      (
                        x M ( x ( join ` K ) y )
                        ->
                        <. x , ( x ( join ` K ) y ) >.
                          I
                        <. ( x ( meet ` K ) y ) , y >.
                      )
                )
              )
            )
          )
        )
      )
    )
  )
  $.
$}

${
  $d K M i s $.

  q2525646-series-definition $a |- (
    Q2525646Series K M s
  ) <->
  (
    s e. Word ( Base ` K )
    /\
    (
      0 < ( # ` s )
      /\
      A. i e. ( 0 ..^ ( ( # ` s ) - 1 ) )
        ( ( s ` i ) M ( s ` ( i + 1 ) ) )
    )
  )
  $.
$}

${
  $d I f i s t $.

  q2525646-equivalent-definition $a |- (
    Q2525646Equivalent I s t
  ) <->
  E. f
    (
      f :
        ( 0 ..^ ( ( # ` s ) - 1 ) )
        -1-1-onto->
        ( 0 ..^ ( ( # ` t ) - 1 ) )
      /\
      A. i e. ( 0 ..^ ( ( # ` s ) - 1 ) )
        (
          <. ( s ` i ) , ( s ` ( i + 1 ) ) >.
            I
          <.
            ( t ` ( f ` i ) ) ,
            ( t ` ( ( f ` i ) + 1 ) )
          >.
        )
    )
  $.
$}

${
  $d I K M s t $.

  thousand-theorems-q2525646-jordan-holder $a |-
    A. K A. M A. I A. s A. t
      (
        (
          Q2525646JHL K M I
          /\
          (
            Q2525646Series K M s
            /\
            (
              Q2525646Series K M t
              /\
              (
                ( s ` 0 ) = ( t ` 0 )
                /\
                ( s ` ( ( # ` s ) - 1 ) )
                  =
                ( t ` ( ( # ` t ) - 1 ) )
              )
            )
          )
        )
        ->
        ( Q2525646Equivalent I s t )
      )
  $.
$}
