$(
  Statement-only formalization of PutnamBench artifact putnam_1962_a4:
  a twice-differentiable real function bounded together with its second
  derivative on an interval of length at least two has first derivative
  bounded in absolute value by two there. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The set.mm class ( RR Dn F ) gives the sequence of iterated real
  derivatives of F. Requiring RR to be contained in the domains of its
  first and second entries expresses the two global differentiability
  assumptions. The final declaration is an unproved $a statement.
$)

${
  $d x A $.
  $d x B $.
  $d x F $.

  putnambench-putnam-1962-a4 $a |- (
    (
      (
        (
          ( A e. RR /\ B e. RR )
          /\
          F : RR --> RR
        )
        /\
        (
          RR C_ dom ( ( RR Dn F ) ` 1 )
          /\
          RR C_ dom ( ( RR Dn F ) ` 2 )
        )
      )
      /\
      (
        (
          A. x e. ( A [,] B )
            ( abs ` ( F ` x ) ) <_ 1
          /\
          A. x e. ( A [,] B )
            ( abs ` ( ( ( RR Dn F ) ` 2 ) ` x ) ) <_ 1
        )
        /\
        2 <_ ( B - A )
      )
    )
    ->
    A. x e. ( A [,] B )
      ( abs ` ( ( ( RR Dn F ) ` 1 ) ` x ) ) <_ 2
  ) $.
$}
