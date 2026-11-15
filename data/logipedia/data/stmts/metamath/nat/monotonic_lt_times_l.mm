$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_lt_times_l
  (logipedia__metamath__nat.monotonic_lt_times_l), catalog title
  "nat.monotonic_lt_times_l": right multiplication by a fixed positive natural
  number is strictly monotone for the natural-number strict order. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's zero, total multiplication, and native strict
  order represent nat.O, nat.times, and nat.lt; on NN0, the latter is
  equivalent to the source definition nat.lt x y := nat.le (nat.S x) y.
  Thus 0 < c is exactly the source positivity assumption. Expanding
  relations.monotonic gives the restricted quantifiers over x and y and the
  inner implication below, while the outer quantifier and implication preserve
  the source binder and hypothesis scope. The final declaration is Metamath's
  native unproved $a statement encoding; this artifact adds no $p proof
  declaration.
$)

logipedia-nat-monotonic-lt-times-l $a |-
  A. c e. NN0
    (
      0 < c
      ->
      A. x e. NN0
        A. y e. NN0
          (
            x < y
            ->
            ( x x. c ) < ( y x. c )
          )
    )
$.
