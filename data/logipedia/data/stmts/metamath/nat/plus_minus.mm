$(
  Statement-only formalization of the Logipedia corpus artifact nat.plus_minus
  (logipedia__metamath__nat.plus_minus), catalog title "nat.plus_minus": for
  all natural numbers m, n, and p with m at most n, the truncated difference
  n minus m plus p equals the truncated difference of n plus p minus m. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition and non-strict order represent
  nat.plus and nat.le. For natural numbers x and y, the term

    if ( y <_ x , x - y , 0 )

  exactly represents the source total subtraction nat.minus x y: ordinary
  subtraction when y is at most x, and zero otherwise. Both subtraction
  occurrences are expanded this way, while native equality represents
  logic.eq at the natural-number type. The three restricted universal
  quantifiers, implication, and equality preserve the source binder order,
  scopes, assumption, and conclusion. The final declaration is Metamath's
  native unproved $a statement encoding; this artifact adds no $p proof
  declaration.
$)

logipedia-nat-plus-minus $a |-
  A. m e. NN0
    A. n e. NN0
      A. p e. NN0
        (
          m <_ n
          ->
          (
            (
              if (
                m <_ n ,
                ( n - m ) ,
                0
              )
              +
              p
            )
            =
            if (
              m <_ ( n + p ) ,
              ( ( n + p ) - m ) ,
              0
            )
          )
        )
$.
