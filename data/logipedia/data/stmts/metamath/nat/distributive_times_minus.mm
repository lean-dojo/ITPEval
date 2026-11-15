$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.distributive_times_minus
  (logipedia__metamath__nat.distributive_times_minus), catalog title
  "nat.distributive_times_minus": left multiplication distributes over
  truncated subtraction on natural numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. For natural numbers u and v, the
  term if ( v <_ u , u - v , 0 ) is exactly the source total subtraction
  nat.minus u v: ordinary subtraction when v is at most u, and zero
  otherwise. SetMM multiplication and equality represent the source times
  operation and natural-number equality. The three restricted universal
  quantifiers preserve the source binder order and scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-distributive-times-minus $a |-
  A. a e. NN0
    A. b e. NN0
      A. c e. NN0
        (
          a
          x.
          if (
            c <_ b ,
            ( b - c ) ,
            0
          )
        )
        =
        if (
          ( a x. c ) <_ ( a x. b ) ,
          ( ( a x. b ) - ( a x. c ) ) ,
          0
        )
$.
