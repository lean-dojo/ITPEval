$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1077462
  (thousand-theorems__metamath__Q1077462), "K&ouml;nig's theorem (set theory)":
  for arbitrary cardinal-valued families over an arbitrary index set,
  pointwise strict inequality makes the cardinal sum strictly smaller than
  the cardinal product. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  m and n are total families on a. Requiring each value to be fixed by card
  says exactly that the families are cardinal-valued. The tagged union
  U_ i e. a ( { i } X. ( m ` i ) ) is the dependent disjoint union whose
  cardinality is the source Cardinal.sum, while X_ i e. a ( n ` i ) is the
  dependent function space whose cardinality is Cardinal.prod. SetMM's ~<
  is strict cardinal domination.

  The final declaration is the single unproved $a corpus statement. This root
  artifact contains no $p declaration; the included lib/set.mm database
  supplies the standard SetMM language and proved library.
$)

${
  $d a i $.  $d i m $.  $d i n $.

  thousand-theorems-q1077462-konig $a |- (
    A. a A. m A. n
      (
        (
          (
            m Fn a
            /\
            n Fn a
          )
          /\
          A. i e. a
            (
              (
                ( card ` ( m ` i ) ) = ( m ` i )
                /\
                ( card ` ( n ` i ) ) = ( n ` i )
              )
              /\
              ( m ` i ) ~< ( n ` i )
            )
        )
        ->
        (
          U_ i e. a ( { i } X. ( m ` i ) )
          ~<
          X_ i e. a ( n ` i )
        )
      )
  ) $.
$}
