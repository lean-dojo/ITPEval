$(
  Statement-only formalization of "The Intermediate Value Theorem" from the
  Hundred Theorems corpus artifact 079. It states that a continuous real
  function on a closed interval attains every real value between its endpoint
  values. This file contains no proof.
$)

$[ library/set.mm $]

$(
  F is a total real function, and its restriction to [A,B] is continuous for
  the usual topology on the real numbers. The weak inequalities include roots
  attained at either endpoint. The final declaration is an unproved $a
  statement.
$)

${
  $d c A $.
  $d c B $.
  $d c F $.
  $d c U $.

  hundred-theorems-079-intermediate-value-theorem $a |- (
    (
      (
        ( A e. RR /\ B e. RR )
        /\
        ( U e. RR /\ A <_ B )
      )
      /\
      (
        F : RR --> RR
        /\
        (
          (
            F |` ( A [,] B )
          )
          e.
          (
            ( ( TopOpen ` RRfld ) |`t ( A [,] B ) )
            Cn
            ( TopOpen ` RRfld )
          )
          /\
          ( ( F ` A ) <_ U /\ U <_ ( F ` B ) )
        )
      )
    )
    ->
    E. c e. ( A [,] B ) ( F ` c ) = U
  ) $.
$}
