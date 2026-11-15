$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2253746
  (thousand-theorems__metamath__Q2253746), "Bertrand's ballot theorem": for
  natural numbers q < p, the uniform probability of integer vote lists with
  p entries equal to +1 and q entries equal to -1 whose every nonempty suffix
  has positive sum is (p - q) / (p + q). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A Lean list of integers is represented by a SetMM word over ZZ, hence by a
  function on a half-open finite ordinal in the same list order.
  Q2253746Counted p q is exactly countedSequence p q: its entries are +1 or
  -1, with the two prescribed occurrence counts.

  Q2253746StaysPositive is exactly staysPositive. For every valid starting
  index k, the sum over k ..^ length is the sum of the corresponding nonempty
  suffix. The empty word satisfies the predicate vacuously, as in the source.

  Q2253746UniformOn S T is the finite uniform measure of T inside S, expressed
  in the extended reals as the cardinality of S intersect T divided by the
  cardinality of S. Under q < p, Q2253746Counted p q is nonempty, so this is
  definitionally the source uniformOn value under the canonical embedding of
  nonnegative finite reals into extended nonnegative reals.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q2253746Counted Q2253746StaysPositive Q2253746UniformOn $.

q2253746-counted-syntax $a class ( Q2253746Counted p q ) $.
q2253746-stays-positive-syntax $a class Q2253746StaysPositive $.
q2253746-uniform-on-syntax $a
  class ( Q2253746UniformOn S T ) $.

${
  $d i p q w $.

  q2253746-counted-definition $a |- (
    Q2253746Counted p q
  ) =
    { w e. Word ZZ |
      (
        (
          ( # `
            { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 1 }
          ) = p
          /\
          ( # `
            { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = -u 1 }
          ) = q
        )
        /\
        A. i e. ( 0 ..^ ( # ` w ) )
          ( ( w ` i ) = 1 \/ ( w ` i ) = -u 1 )
      )
    }
  $.
$}

${
  $d i k w $.

  q2253746-stays-positive-definition $a |-
    Q2253746StaysPositive =
    { w e. Word ZZ |
      A. k e. ( 0 ..^ ( # ` w ) )
        0 < sum_ i e. ( k ..^ ( # ` w ) ) ( w ` i )
    }
  $.
$}

${
  q2253746-uniform-on-definition $a |- (
    Q2253746UniformOn S T
  ) =
    (
      ( # ` ( S i^i T ) )
      /e
      ( # ` S )
    )
  $.
$}

${
  $d i k p q w $.

  thousand-theorems-q2253746-bertrand-ballot $a |-
    A. q e. NN0
      A. p e. NN0
        (
          q < p
          ->
          (
            (
              Q2253746UniformOn
                ( Q2253746Counted p q )
                Q2253746StaysPositive
            )
            =
            ( ( p - q ) /e ( p + q ) )
          )
        )
  $.
$}
