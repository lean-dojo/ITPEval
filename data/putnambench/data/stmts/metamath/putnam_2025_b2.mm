$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_b2: the x-coordinate of the centroid of the solid obtained by
  rotating the region under a nonnegative strictly increasing continuous
  function on the unit interval exceeds the region's centroid x-coordinate.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions. Its restriction to [0,1]
  is required to be continuous, and the restricted universal quantifiers
  state nonnegativity and strict increase exactly on that interval.

  Set.mm's S. binder is the real Lebesgue integral. For these continuous
  integrands, integration over the closed unit interval agrees with Lean's
  interval integral from 0 to 1 because endpoints have measure zero. The
  two displayed quotients are respectively the region and rotated-solid
  centroid x-coordinates; the common rotational factor pi cancels from the
  second quotient.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d F x y $.

  putnambench-putnam-2025-b2 $a |- A. F e. ( RR ^m RR )
    (
      (
        (
          ( F |` ( 0 [,] 1 ) )
          e.
          ( ( 0 [,] 1 ) -cn-> RR )
        )
        /\
        (
          A. x e. ( 0 [,] 1 )
            0 <_ ( F ` x )
          /\
          A. x e. ( 0 [,] 1 )
            A. y e. ( 0 [,] 1 )
              (
                x < y
                ->
                ( F ` x ) < ( F ` y )
              )
        )
      )
      ->
      (
        (
          S. ( 0 [,] 1 )
            ( x x. ( F ` x ) )
            _d x
          /
          S. ( 0 [,] 1 )
            ( F ` x )
            _d x
        )
        <
        (
          S. ( 0 [,] 1 )
            ( x x. ( ( F ` x ) ^ 2 ) )
            _d x
          /
          S. ( 0 [,] 1 )
            ( ( F ` x ) ^ 2 )
            _d x
        )
      )
    )
  $.
$}
