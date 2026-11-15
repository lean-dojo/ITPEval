$(
  Statement-only formalization of "The Mean Value Theorem" from Hundred
  Theorems corpus artifact 075. It states Lagrange's theorem for a real
  function continuous on a closed interval with a specified derivative on
  its interior. This file contains no proof.
$)

$[ library/set.mm $]

$(
  F and G are total real functions, with G giving the derivative of F at
  every point of the open interval (A,B). Continuity is expressed for the
  restriction of F to [A,B] using the subspace topology. The conclusion uses
  the endpoint-difference form, equivalent to equality with the secant slope
  because A < B. The final declaration is an unproved $a statement.
$)

${
  $d c A $.
  $d c B $.
  $d c F $.
  $d c G $.
  $d c x $.
  $d x A $.
  $d x B $.
  $d x F $.
  $d x G $.

  hundred-theorems-075-mean-value-theorem $a |- (
    (
      (
        ( A e. RR /\ B e. RR )
        /\
        ( A < B /\ ( F : RR --> RR /\ G : RR --> RR ) )
      )
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
        A. x e. ( A (,) B )
          (
            x e. dom ( RR _D F )
            /\
            ( ( RR _D F ) ` x ) = ( G ` x )
          )
      )
    )
    ->
    E. c e. ( A (,) B )
      (
        ( ( F ` B ) - ( F ` A ) )
        =
        ( ( B - A ) x. ( G ` c ) )
      )
  ) $.
$}
