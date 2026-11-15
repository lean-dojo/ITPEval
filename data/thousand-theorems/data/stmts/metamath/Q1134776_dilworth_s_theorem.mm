$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1134776
  (thousand-theorems__metamath__Q1134776), "Dilworth's theorem": on every
  finite partially ordered set, the minimum number of chains in a partition
  equals the maximum cardinality of an antichain. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite Lean type is represented by an arbitrary finite set A, and its
  partial order by a relation R on A. Q1134776Chain and
  Q1134776Antichain are the corresponding pairwise comparability and
  incomparability predicates. Q1134776ChainPartition requires a unique chain
  block containing each element of A.

  Q1134776MinChainNumber A R k says that k is attained by a chain partition
  and is no larger than the cardinality of any chain partition.
  Q1134776AntichainWidth A R k says that k is attained by an antichain and
  bounds the cardinality of every antichain. For finite A these predicates
  uniquely characterize the natural values of the source ENat definitions.
  Thus the shared existential k in the final declaration is bidirectionally
  equivalent to minChainPartition = antichainWidth, including when A is empty.

  The final declaration is the single unproved corpus $a statement. All
  preceding root-artifact $a declarations are syntax or faithful definitions,
  and this root artifact introduces no $p proof statement.
$)

$c Q1134776PartialOrder Q1134776Chain Q1134776Antichain
   Q1134776ChainPartition Q1134776MinChainNumber
   Q1134776AntichainWidth $.

q1134776-partial-order-syntax $a
  wff ( Q1134776PartialOrder A R ) $.
q1134776-chain-syntax $a
  wff ( Q1134776Chain A R C ) $.
q1134776-antichain-syntax $a
  wff ( Q1134776Antichain A R B ) $.
q1134776-chain-partition-syntax $a
  wff ( Q1134776ChainPartition A R P ) $.
q1134776-min-chain-number-syntax $a
  wff ( Q1134776MinChainNumber A R k ) $.
q1134776-antichain-width-syntax $a
  wff ( Q1134776AntichainWidth A R k ) $.

${
  $d A R x y z $.

  q1134776-partial-order-definition $a |- (
    ( Q1134776PartialOrder A R )
    <->
    (
      R C_ ( A X. A )
      /\
      (
        A. x e. A x R x
        /\
        (
          A. x e. A A. y e. A
            ( ( x R y /\ y R x ) -> x = y )
          /\
          A. x e. A A. y e. A A. z e. A
            ( ( x R y /\ y R z ) -> x R z )
        )
      )
    )
  ) $.
$}

${
  $d A C R x y $.

  q1134776-chain-definition $a |- (
    ( Q1134776Chain A R C )
    <->
    (
      C C_ A
      /\
      A. x e. C A. y e. C
        ( x =/= y -> ( x R y \/ y R x ) )
    )
  ) $.
$}

${
  $d A B R x y $.

  q1134776-antichain-definition $a |- (
    ( Q1134776Antichain A R B )
    <->
    (
      B C_ A
      /\
      A. x e. B A. y e. B
        ( x =/= y -> -. x R y )
    )
  ) $.
$}

${
  $d A P R c x $.

  q1134776-chain-partition-definition $a |- (
    ( Q1134776ChainPartition A R P )
    <->
    (
      P C_ ~P A
      /\
      (
        A. x e. A E! c e. P x e. c
        /\
        A. c e. P ( Q1134776Chain A R c )
      )
    )
  ) $.
$}

${
  $d A R k p q $.

  q1134776-min-chain-number-definition $a |- (
    ( Q1134776MinChainNumber A R k )
    <->
    (
      k e. NN0
      /\
      E. p
        (
          ( Q1134776ChainPartition A R p )
          /\
          (
            ( # ` p ) = k
            /\
            A. q
              (
                ( Q1134776ChainPartition A R q )
                ->
                k <_ ( # ` q )
              )
          )
        )
    )
  ) $.
$}

${
  $d A R b c k $.

  q1134776-antichain-width-definition $a |- (
    ( Q1134776AntichainWidth A R k )
    <->
    (
      k e. NN0
      /\
      E. b
        (
          ( Q1134776Antichain A R b )
          /\
          (
            ( # ` b ) = k
            /\
            A. c
              (
                ( Q1134776Antichain A R c )
                ->
                ( # ` c ) <_ k
              )
          )
        )
    )
  ) $.
$}

${
  $d a k r $.

  thousand-theorems-q1134776-dilworth $a |- (
    A. a A. r
      (
        (
          a e. Fin
          /\
          ( Q1134776PartialOrder a r )
        )
        ->
        E. k e. NN0
          (
            ( Q1134776MinChainNumber a r k )
            /\
            ( Q1134776AntichainWidth a r k )
          )
      )
  ) $.
$}
