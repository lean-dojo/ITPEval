$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_b4: a real number greater than one satisfying
  x = 2207 - 1/x has eighth root (3 + sqrt(5)) / 2. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The Rocq source defines the annotated integer solution tuple as
  (3, 1, 5, 2), while the Lean and Isabelle sources record the same tuple
  in comments. It is inlined in the conclusion as (3 + sqrt(5)) / 2.

  The hypothesis x > 1 makes the base positive, so set.mm's complex-power
  operation x ^c (1 / 8) is real-valued and equals the source real eighth
  power. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

putnambench-putnam-1995-b4 $a |- A. x e. RR
  (
    (
      x = ( ; ; ; 2 2 0 7 - ( 1 / x ) )
      /\
      1 < x
    )
    ->
    (
      x ^c ( 1 / 8 )
    )
    =
    (
      ( 3 + ( sqrt ` 5 ) )
      /
      2
    )
  )
$.
