$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_b2: a strict factorial-to-power inequality for two positive
  integers and their sum. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, so the two restricted universal
  quantifiers are equivalent to the source's natural-number parameters
  together with the assumptions m > 0 and n > 0. Factorial, natural
  exponentiation, division, multiplication, and strict order retain their
  standard rational values; hence the displayed inequality is exactly the
  rational inequality in the primary Lean source (and equivalently the real
  inequality in Rocq).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d m n $.

  putnambench-putnam-2004-b2 $a |-
    A. m e. NN A. n e. NN
      (
        ( ( ! ` ( m + n ) ) / ( ( m + n ) ^ ( m + n ) ) )
        <
        (
          ( ( ! ` m ) / ( m ^ m ) )
          x.
          ( ( ! ` n ) / ( n ^ n ) )
        )
      )
  $.
$}
