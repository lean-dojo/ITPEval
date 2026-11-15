$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_a5: the greatest number of uncovered squares that Alice can
  guarantee in the 2022-square adjacent-domino game is 290. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P22A5I is the 2022-element ordinal representing Fin 2022, and
  P22A5States is its full powerset. P22A5Move X Y directly expands the
  source move predicate: either X is terminal and Y = X, or Y adds one
  uncovered adjacent pair. The terminal clause retains the source condition
  that every uncovered square below 2021 has its successor covered.

  A word over P22A5States is exactly a finite list of board states, with
  # ` G its length. P22A5Game requires a nonempty word starting at the empty
  board and applies P22A5Move to every consecutive pair. P22A5Conforms
  requires the strategy move at each even-indexed turn, exactly as in the
  source. Strategies remain arbitrary total functions on the full state
  space.

  P22A5Good n says that some such strategy guarantees at least n uncovered
  squares for every conforming valid game. Since every valid game is
  nonempty, using its last entry G((# ` G)-1) is bidirectionally equivalent
  to the source's existential prefix-and-last decomposition. The final
  conjunction expands IsGreatest for the annotated solution 290. Every
  declaration below is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c P22A5I P22A5States P22A5Move P22A5Game P22A5Conforms P22A5Good $.

p22a5-index-syntax $a class P22A5I $.
p22a5-states-syntax $a class P22A5States $.
p22a5-move-syntax $a wff ( P22A5Move X Y ) $.
p22a5-game-syntax $a wff ( P22A5Game G ) $.
p22a5-conforms-syntax $a wff ( P22A5Conforms G S ) $.
p22a5-good-syntax $a wff ( P22A5Good n ) $.

p22a5-index-definition $a |-
  P22A5I = ( 0 ..^ ; ; ; 2 0 2 2 )
$.

p22a5-states-definition $a |-
  P22A5States = ( ~P P22A5I )
$.

${
  $d X Y i $.

  p22a5-move-definition $a |- (
    ( P22A5Move X Y )
    <->
    (
      (
        X = Y
        /\
        A. i e. ( 0 ..^ ; ; ; 2 0 2 1 )
          (
            i e/ X
            ->
            ( i + 1 ) e. X
          )
      )
      \/
      E. i e. ( 0 ..^ ; ; ; 2 0 2 1 )
        (
          i e/ X
          /\
          (
            ( i + 1 ) e/ X
            /\
            Y = ( X u. { i , ( i + 1 ) } )
          )
        )
    )
  ) $.
$}

${
  $d G i $.

  p22a5-game-definition $a |- (
    ( P22A5Game G )
    <->
    (
      G e. ( Word P22A5States \ { (/) } )
      /\
      (
        ( G ` 0 ) = (/)
        /\
        A. i e. ( 0 ..^ ( ( # ` G ) - 1 ) )
          ( P22A5Move ( G ` i ) ( G ` ( i + 1 ) ) )
      )
    )
  ) $.
$}

${
  $d G S i $.

  p22a5-conforms-definition $a |- (
    ( P22A5Conforms G S )
    <->
    A. i e. ( 0 ..^ ( ( # ` G ) - 1 ) )
      (
        2 || i
        ->
        ( G ` ( i + 1 ) ) = ( S ` ( G ` i ) )
      )
  ) $.
$}

${
  $d G S X n $.

  p22a5-good-definition $a |- (
    ( P22A5Good n )
    <->
    E. S e. ( P22A5States ^m P22A5States )
      (
        A. X e. P22A5States
          ( P22A5Move X ( S ` X ) )
        /\
        A. G e. ( Word P22A5States )
          (
            (
              ( P22A5Game G )
              /\
              ( P22A5Conforms G S )
            )
            ->
            n
            <_
            (
              #
              `
              (
                P22A5I
                \
                ( G ` ( ( # ` G ) - 1 ) )
              )
            )
          )
      )
  ) $.
$}

putnambench-putnam-2022-a5 $a |- (
  ( P22A5Good ; ; 2 9 0 )
  /\
  A. n e. NN0
    (
      ( P22A5Good n )
      ->
      n <_ ; ; 2 9 0
    )
) $.
