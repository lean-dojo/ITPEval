$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_a1: every binary operation satisfying (a * b) * a = b also
  satisfies a * (b * a) = b on its arbitrary carrier. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary carrier is the set S, and F is an arbitrary total binary
  operation represented as a function from S X. S to S. Application to an
  ordered pair represents the source operation. The antecedent and conclusion
  retain the source's universal quantifiers and the two operation identities
  exactly.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F S a b $.

  putnambench-putnam-2001-a1 $a |- A. S
    A. F e. ( S ^m ( S X. S ) )
      (
        A. a e. S A. b e. S
          ( F ` <. ( F ` <. a , b >. ) , a >. ) = b
        ->
        A. a e. S A. b e. S
          ( F ` <. a , ( F ` <. b , a >. ) >. ) = b
      )
  $.
$}
