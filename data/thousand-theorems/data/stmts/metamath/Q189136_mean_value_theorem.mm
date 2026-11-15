$(
  Statement-only formalization of Thousand Theorems corpus artifact Q189136
  (thousand-theorems__metamath__Q189136), "Mean value theorem": Cauchy's
  two-function and Lagrange's one-function mean value theorems for real
  functions continuous on a closed interval and differentiable on its
  interior. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Membership in RR ^m RR gives total real-valued functions. Continuity of
  each restriction to [A,B] is expressed between the interval's subspace
  topology and the real topology. Membership of x in dom ( RR _D F ) is
  SetMM's native assertion that F is differentiable at x, and applying that
  derivative function gives its value there. Since every interior point is
  required to belong to the derivative domain, these values agree exactly
  with Mathlib's totalized deriv at every point used in either conclusion.

  The first final $a declaration is Cauchy's cross-multiplied equality, which
  requires no nonvanishing derivative assumption. The second is Lagrange's
  equality with the secant slope. Both witnesses remain existentially
  quantified in the open interval, and both declarations are unproved
  statement encodings.
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

  thousand-theorems-metamath-Q189136-cauchy-mean-value-theorem $a |-
    A. A e. RR
      A. B e. RR
        A. F e. ( RR ^m RR )
          A. G e. ( RR ^m RR )
            (
              (
                (
                  A < B
                  /\
                  (
                    F |` ( A [,] B )
                  )
                  e.
                  (
                    ( ( TopOpen ` RRfld ) |`t ( A [,] B ) )
                    Cn
                    ( TopOpen ` RRfld )
                  )
                )
                /\
                (
                  (
                    G |` ( A [,] B )
                  )
                  e.
                  (
                    ( ( TopOpen ` RRfld ) |`t ( A [,] B ) )
                    Cn
                    ( TopOpen ` RRfld )
                  )
                )
              )
              /\
              (
                (
                  A. x e. ( A (,) B )
                    x e. dom ( RR _D F )
                )
                /\
                (
                  A. x e. ( A (,) B )
                    x e. dom ( RR _D G )
                )
              )
              ->
              E. c e. ( A (,) B )
                (
                  (
                    ( ( G ` B ) - ( G ` A ) )
                    x.
                    ( ( RR _D F ) ` c )
                  )
                  =
                  (
                    ( ( F ` B ) - ( F ` A ) )
                    x.
                    ( ( RR _D G ) ` c )
                  )
                )
            ) $.
$}

${
  $d c A $.
  $d c B $.
  $d c F $.
  $d c x $.
  $d x A $.
  $d x B $.
  $d x F $.

  thousand-theorems-metamath-Q189136-lagrange-mean-value-theorem $a |-
    A. A e. RR
      A. B e. RR
        A. F e. ( RR ^m RR )
          (
            (
              (
                A < B
                /\
                (
                  F |` ( A [,] B )
                )
                e.
                (
                  ( ( TopOpen ` RRfld ) |`t ( A [,] B ) )
                  Cn
                  ( TopOpen ` RRfld )
                )
              )
              /\
              (
                A. x e. ( A (,) B )
                  x e. dom ( RR _D F )
              )
            )
            ->
            E. c e. ( A (,) B )
              (
                ( ( RR _D F ) ` c )
                =
                (
                  ( ( F ` B ) - ( F ` A ) )
                  /
                  ( B - A )
                )
              )
          ) $.
$}
