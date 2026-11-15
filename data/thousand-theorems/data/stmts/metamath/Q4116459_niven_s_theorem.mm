$(
  Statement-only formalization of Thousand Theorems corpus artifact Q4116459
  (thousand-theorems__metamath__Q4116459), "Niven's theorem": every real angle
  that is a rational multiple of pi and has rational cosine has cosine equal
  to -1, -1/2, 0, 1/2, or 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The included set.mm library supplies the standard real numbers RR, rational
  numbers QQ, pi _pi, real cosine, arithmetic, equality, and restricted
  quantifiers. The two existential quantifiers preserve the rational
  witnesses internal to the source hypotheses. The five-way disjunction is
  exactly membership in the source's five-element set.

  The final $a declaration is the single unproved corpus statement; there is
  no $p proof statement.
$)

${
  $d q r t $.

  thousand-theorems-q4116459-niven $a |- A. t e. RR
    (
      (
        E. r e. QQ t = ( r x. _pi )
        /\
        E. q e. QQ ( cos ` t ) = q
      )
      ->
      (
        ( cos ` t ) = ( -u 1 )
        \/
        ( cos ` t ) = ( ( -u 1 ) / 2 )
        \/
        ( cos ` t ) = 0
        \/
        ( cos ` t ) = ( 1 / 2 )
        \/
        ( cos ` t ) = 1
      )
    )
  $.
$}
