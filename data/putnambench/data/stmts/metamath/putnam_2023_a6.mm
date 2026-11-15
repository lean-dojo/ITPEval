$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_a6: Bob has a strategy and a fixed parity goal that wins the
  alternating permutation game for every positive number of available
  integers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A complete n-turn game is represented by a bijection from the zero-based
  turn indices 0 ..^ n onto the chosen integers 1 ... n. A strategy is a
  total function on finite words over 1 ... n. At every odd-length injective
  prefix shorter than n, validity requires the strategy to choose an integer
  outside the prefix range. Conformance applies the strategy exactly at the
  odd zero-based indices, which are Bob's turns.

  P23A6Winning n keeps both the strategy and Bob's parity goal internally
  existential. The fixed-point set counts the turns i at which integer i+1
  is chosen, so its cardinality modulo two is the game's winning parity.
  The final assertion is the source solution-set equality. All declarations
  are unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P23A6Solution P23A6Game P23A6ValidStrategy P23A6Conforms
   P23A6Winning $.

p23a6-solution-syntax $a class P23A6Solution $.
p23a6-game-syntax $a wff ( P23A6Game n G ) $.
p23a6-valid-strategy-syntax $a wff ( P23A6ValidStrategy n S ) $.
p23a6-conforms-syntax $a wff ( P23A6Conforms n G S ) $.
p23a6-winning-syntax $a wff ( P23A6Winning n ) $.

p23a6-solution-definition $a |- P23A6Solution = NN $.

${
  $d G n $.

  p23a6-game-definition $a |- (
    ( P23A6Game n G )
    <->
    G : ( 0 ..^ n ) -1-1-onto-> ( 1 ... n )
  ) $.
$}

${
  $d H S n $.

  p23a6-valid-strategy-definition $a |- (
    ( P23A6ValidStrategy n S )
    <->
    (
      S e. ( ( 1 ... n ) ^m ( Word ( 1 ... n ) ) )
      /\
      A. H e. ( Word ( 1 ... n ) )
        (
          (
            (
              H : ( 0 ..^ ( # ` H ) ) -1-1-> ( 1 ... n )
              /\
              ( # ` H ) < n
            )
            /\
            ( ( # ` H ) mod 2 ) = 1
          )
          ->
          ( S ` H ) e/ ran H
        )
    )
  ) $.
$}

${
  $d G S i n $.

  p23a6-conforms-definition $a |- (
    ( P23A6Conforms n G S )
    <->
    A. i e. ( 0 ..^ n )
      (
        ( i mod 2 ) = 1
        ->
        ( G ` i ) = ( S ` ( G |` ( 0 ..^ i ) ) )
      )
  ) $.
$}

${
  $d G S i n p $.

  p23a6-winning-definition $a |- (
    ( P23A6Winning n )
    <->
    E. S
      (
        ( P23A6ValidStrategy n S )
        /\
        E. p e. ( 0 ..^ 2 )
          A. G
            (
              (
                ( P23A6Game n G )
                /\
                ( P23A6Conforms n G S )
              )
              ->
              (
                (
                  #
                  `
                  {
                    i e. ( 0 ..^ n ) |
                    ( G ` i ) = ( i + 1 )
                  }
                )
                mod 2
              )
              =
              p
            )
      )
  ) $.
$}

putnambench-putnam-2023-a6 $a |- (
  {
    n e. NN0 |
    (
      0 < n
      /\
      ( P23A6Winning n )
    )
  }
  =
  P23A6Solution
) $.
