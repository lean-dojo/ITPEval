$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_a3 (putnambench__metamath__putnam_2025_a3): Bob wins the
  no-repetition game on length-n ternary strings for every positive n, where
  each move changes exactly one digit by one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P25A3States n is the full function space from the n zero-based positions
  to {0,1,2}; no finite table replaces this state space. P25A3Initial n is
  the constant-zero state. P25A3Move requires a unique changed coordinate
  and a difference of exactly one there.

  P25A3Play states the source Chain condition from the initial state and
  the source Nodup condition: the word of played states is injective and
  omits the initial state. P25A3Win is the intersection characterization
  of the inductively generated HasWinningStrategy predicate. Namely, a
  history belongs to every set of histories closed under the source win
  constructor. This is the standard least-constructor-closed encoding and
  preserves the existential move, universal reply, and recursive scopes.

  P25A3Solution is False, as specified by the source solution annotation.
  The final declaration is the single unproved corpus assertion. Every $a
  declaration in this file is statement syntax or a faithful definition;
  there is no $p proof declaration.
$)

$c P25A3States P25A3Initial P25A3UniqueChange P25A3Move P25A3Play
   P25A3Win P25A3Solution $.

p25a3-states-syntax $a class ( P25A3States n ) $.
p25a3-initial-syntax $a class ( P25A3Initial n ) $.
p25a3-unique-change-syntax $a wff ( P25A3UniqueChange n s t ) $.
p25a3-move-syntax $a wff ( P25A3Move n s t ) $.
p25a3-play-syntax $a wff ( P25A3Play n P ) $.
p25a3-win-syntax $a wff ( P25A3Win n P ) $.
p25a3-solution-syntax $a wff ( P25A3Solution n ) $.

p25a3-states-definition $a |- (
  P25A3States n
  =
  ( ( 0 ... 2 ) ^m ( 0 ..^ n ) )
) $.

${
  $d i n $.

  p25a3-initial-definition $a |- (
    P25A3Initial n
    =
    ( i e. ( 0 ..^ n ) |-> 0 )
  ) $.
$}

${
  $d i n s t $.

  p25a3-unique-change-definition $a |- (
    ( P25A3UniqueChange n s t )
    <->
    E! i e. ( 0 ..^ n )
      ( s ` i ) =/= ( t ` i )
  ) $.
$}

${
  $d i n s t $.

  p25a3-move-definition $a |- (
    ( P25A3Move n s t )
    <->
    (
      (
        s e. ( P25A3States n )
        /\
        t e. ( P25A3States n )
      )
      /\
      (
        ( P25A3UniqueChange n s t )
        /\
        A. i e. ( 0 ..^ n )
          (
            ( s ` i ) =/= ( t ` i )
            ->
            (
              ( ( s ` i ) + 1 ) = ( t ` i )
              \/
              ( ( t ` i ) + 1 ) = ( s ` i )
            )
          )
      )
    )
  ) $.
$}

${
  $d P i k n $.

  p25a3-play-definition $a |- (
    ( P25A3Play n P )
    <->
    (
      P e. Word ( P25A3States n )
      /\
      (
        A. k e. ( 0 ..^ ( # ` P ) )
          (
            P25A3Move n
              if ( k = 0 ,
                   ( P25A3Initial n ) ,
                   ( P ` ( k - 1 ) ) )
              ( P ` k )
          )
        /\
        (
          P : ( 0 ..^ ( # ` P ) ) -1-1-> ( P25A3States n )
          /\
          ( P25A3Initial n ) e/ ran P
        )
      )
    )
  ) $.
$}

${
  $d P Q R n s t $.

  p25a3-win-definition $a |- (
    ( P25A3Win n P )
    <->
    A. R
      (
        A. Q e. Word ( P25A3States n )
          (
            (
              E. s e. ( P25A3States n )
                (
                  P25A3Play n ( Q ++ <" s "> )
                  /\
                  A. t e. ( P25A3States n )
                    (
                      P25A3Play n
                        ( ( Q ++ <" s "> ) ++ <" t "> )
                      ->
                      ( ( Q ++ <" s "> ) ++ <" t "> ) e. R
                    )
                )
            )
            ->
            Q e. R
          )
        ->
        P e. R
      )
  ) $.
$}

p25a3-solution-definition $a |- (
  ( P25A3Solution n )
  <->
  F.
) $.

putnambench-putnam-2025-a3 $a |- A. n e. NN0
  (
    1 <_ n
    ->
    (
      ( P25A3Solution n )
      <->
      ( P25A3Win n (/) )
    )
  )
$.
