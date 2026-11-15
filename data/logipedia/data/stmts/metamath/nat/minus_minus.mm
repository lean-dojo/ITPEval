$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_minus (logipedia__metamath__nat.minus_minus), catalog title
  "nat.minus_minus": for natural numbers p, m, and n with p at most m and
  m at most n, p plus the truncated difference n minus m equals n minus the
  truncated difference m minus p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition and non-strict order represent
  nat.plus and nat.le. For natural numbers x and y, the term

    if ( y <_ x , x - y , 0 )

  exactly represents the source total subtraction nat.minus x y: ordinary
  subtraction when y is at most x, and zero otherwise. Expanding all three
  source subtraction terms this way preserves their truncated semantics.
  Native equality represents logic.eq at the natural-number type. The three
  restricted universal quantifiers and the two nested implications preserve
  the source binder order, scopes, assumptions, and conclusion. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-minus-minus $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        (
          p <_ m
          ->
          (
            m <_ n
            ->
            (
              p
              +
              if (
                m <_ n ,
                ( n - m ) ,
                0
              )
            )
            =
            if (
              if (
                p <_ m ,
                ( m - p ) ,
                0
              )
              <_
              n ,
              (
                n
                -
                if (
                  p <_ m ,
                  ( m - p ) ,
                  0
                )
              ) ,
              0
            )
          )
        )
$.
