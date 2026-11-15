$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_15, catalog title increasingTriplet: an executable greedy
  scan of a finite integer list decides whether three entries at increasing
  indices have strictly increasing values, together with its Boolean
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, Word ZZ is exactly the type of
  arbitrary finite integer lists, and { 0 , 1 } represents Bool with false
  = 0 and true = 1. For a word w, # ` w is its length, w ` k is zero-based
  lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA15None, VERINA15Some, and VERINA15OptionInt give a disjoint tagged
  encoding of Option Int. VERINA15State is the pair of optional first and
  second candidates maintained by the source loop. VERINA15NoHitStep is
  exactly one recursive branch that continues scanning, while VERINA15Hit
  is exactly the final branch that returns true.

  VERINA15LoopGraph records the exact finite execution of the local loop.
  Its true branch contains all preceding non-hit transitions followed by
  the first successful input position; its false branch contains one
  non-hit transition for every input entry. VERINA15Loop selects the unique
  Boolean output of this graph. VERINA15IncreasingTriplet also retains the
  source's explicit length-below-three guard, so this is the executable
  program semantics on every typed input, not an unconstrained output
  relation and not a choice made from the postcondition.

  VERINA15Pre is the source True precondition together with the List Int
  input type. VERINA15Post reproduces both nested zipIdx any/all clauses:
  true implies an increasing indexed triplet, and false implies that every
  indexed triple violates at least one required inequality. The proof-valued
  precondition argument is computationally unused and is omitted from the
  target function. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and
  this database has no $p declaration.
$)

$c
  VERINA15None VERINA15Some VERINA15OptionInt
  VERINA15State VERINA15Initial
  VERINA15Hit VERINA15NoHitStep
  VERINA15LoopGraph VERINA15Loop VERINA15IncreasingTriplet
  VERINA15Pre VERINA15Post
$.

verina15-none-syntax $a class VERINA15None $.
verina15-some-syntax $a class ( VERINA15Some A ) $.
verina15-option-int-syntax $a class VERINA15OptionInt $.
verina15-state-syntax $a class VERINA15State $.
verina15-initial-syntax $a class VERINA15Initial $.
verina15-hit-syntax $a wff ( VERINA15Hit A B ) $.
verina15-no-hit-step-syntax
  $a wff ( VERINA15NoHitStep A B C ) $.
verina15-loop-graph-syntax
  $a wff ( VERINA15LoopGraph A B ) $.
verina15-loop-syntax $a class ( VERINA15Loop A ) $.
verina15-increasing-triplet-syntax
  $a class ( VERINA15IncreasingTriplet A ) $.
verina15-precondition-syntax $a wff ( VERINA15Pre A ) $.
verina15-postcondition-syntax $a wff ( VERINA15Post A B ) $.

verina15-none-definition $a |- VERINA15None = (/) $.

verina15-some-definition $a |- (
  VERINA15Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina15-option-int-definition $a |- VERINA15OptionInt =
    { x |
      (
        x = VERINA15None
        \/
        E. y e. ZZ x = ( VERINA15Some y )
      )
    } $.
$}

verina15-state-definition $a |- VERINA15State = (
  VERINA15OptionInt X. VERINA15OptionInt
) $.

verina15-initial-definition $a |- VERINA15Initial = <.
  VERINA15None , VERINA15None
>. $.

${
  $d f s A B $.

  verina15-hit-definition $a |- (
    VERINA15Hit A B
  ) <-> (
    (
      A e. VERINA15State
      /\
      B e. ZZ
    )
    /\
    E. f e. ZZ E. s e. ZZ
      (
        (
          ( 1st ` A ) = ( VERINA15Some f )
          /\
          ( 2nd ` A ) = ( VERINA15Some s )
        )
        /\
        (
          f < B
          /\
          s < B
        )
      )
  ) $.
$}

${
  $d f s A B C $.

  verina15-no-hit-step-definition $a |- (
    VERINA15NoHitStep A B C
  ) <-> (
    (
      (
        A e. VERINA15State
        /\
        B e. ZZ
      )
      /\
      C e. VERINA15State
    )
    /\
    (
      (
        ( 1st ` A ) = VERINA15None
        /\
        C = <. ( VERINA15Some B ) , VERINA15None >.
      )
      \/
      E. f e. ZZ
        (
          (
            ( 1st ` A ) = ( VERINA15Some f )
            /\
            B <_ f
          )
          /\
          C = <. ( VERINA15Some B ) , ( 2nd ` A ) >.
        )
      \/
      E. f e. ZZ
        (
          (
            (
              ( 1st ` A ) = ( VERINA15Some f )
              /\
              f < B
            )
            /\
            ( 2nd ` A ) = VERINA15None
          )
          /\
          C = <. ( 1st ` A ) , ( VERINA15Some B ) >.
        )
      \/
      E. f e. ZZ E. s e. ZZ
        (
          (
            (
              ( 1st ` A ) = ( VERINA15Some f )
              /\
              f < B
            )
            /\
            (
              ( 2nd ` A ) = ( VERINA15Some s )
              /\
              B <_ s
            )
          )
          /\
          C = <. ( 1st ` A ) , ( VERINA15Some B ) >.
        )
    )
  ) $.
$}

${
  $d i k t A B $.

  verina15-loop-graph-definition $a |- (
    VERINA15LoopGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      (
        B = 1
        /\
        E. k e. ( 0 ..^ ( # ` A ) )
          E. t e. Word VERINA15State
            (
              (
                ( # ` t ) = ( k + 1 )
                /\
                ( t ` 0 ) = VERINA15Initial
              )
              /\
              (
                A. i e. ( 0 ..^ k )
                  (
                    VERINA15NoHitStep
                      ( t ` i )
                      ( A ` i )
                      ( t ` ( i + 1 ) )
                  )
                /\
                ( VERINA15Hit ( t ` k ) ( A ` k ) )
              )
            )
      )
      \/
      (
        B = 0
        /\
        E. t e. Word VERINA15State
          (
            (
              ( # ` t ) = ( ( # ` A ) + 1 )
              /\
              ( t ` 0 ) = VERINA15Initial
            )
            /\
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                VERINA15NoHitStep
                  ( t ` k )
                  ( A ` k )
                  ( t ` ( k + 1 ) )
              )
          )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina15-loop-definition $a |- (
    VERINA15Loop A
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA15LoopGraph A y )
  ) $.
$}

verina15-increasing-triplet-definition $a |- (
  VERINA15IncreasingTriplet A
) = if (
  ( # ` A ) < 3 ,
  0 ,
  ( VERINA15Loop A )
) $.

verina15-precondition-definition $a |- (
  VERINA15Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i j k A B $.

  verina15-postcondition-definition $a |- (
    VERINA15Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      (
        B = 1
        ->
        E. i e. ( 0 ..^ ( # ` A ) )
          E. j e. ( 0 ..^ ( # ` A ) )
            E. k e. ( 0 ..^ ( # ` A ) )
              (
                (
                  i < j
                  /\
                  j < k
                )
                /\
                (
                  ( A ` i ) < ( A ` j )
                  /\
                  ( A ` j ) < ( A ` k )
                )
              )
      )
      /\
      (
        B = 0
        ->
        A. i e. ( 0 ..^ ( # ` A ) )
          A. j e. ( 0 ..^ ( # ` A ) )
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                j <_ i
                \/
                k <_ j
                \/
                ( A ` j ) <_ ( A ` i )
                \/
                ( A ` k ) <_ ( A ` j )
              )
      )
    )
  ) $.
$}

verina-advanced-15-increasing-triplet $a |- A. w e. Word ZZ
  (
    ( VERINA15Pre w )
    ->
    (
      VERINA15Post
        w
        ( VERINA15IncreasingTriplet w )
    )
  )
$.
