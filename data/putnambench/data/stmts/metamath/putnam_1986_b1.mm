$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_b1: an inscribed rectangle of height h and an oppositely pointed
  isosceles triangle share base b and have equal area when h is 2 / 5. This
  statement artifact contains no proof; its root file has no $p statement,
  while the included set.mm library contains proofs.
$)

$[ lib/set.mm $]

$(
  The restricted quantifiers preserve the source variables b and h as real
  numbers. The antecedent retains their positivity, the circle equation, and
  the supplied equal-area equation. The decimal 0.5 is written exactly as
  1 / 2, and the ground-truth solution annotation is inlined as 2 / 5.

  The final declaration is the artifact's single unproved $a corpus statement.
  This root file declares no $p statement; the included set.mm library contains
  proofs.
$)

${
  $d b h $.

  putnambench-putnam-1986-b1 $a |- A. b e. RR A. h e. RR
    (
      (
        (
          (
            0 < b
            /\
            0 < h
          )
          /\
          (
            ( b ^ 2 )
            +
            ( h ^ 2 )
          )
          =
          ( 2 ^ 2 )
        )
        /\
        (
          b x. h
        )
        =
        (
          (
            ( 1 / 2 )
            x.
            b
          )
          x.
          (
            1
            -
            ( h / 2 )
          )
        )
      )
      ->
      h = ( 2 / 5 )
    )
  $.
$}
