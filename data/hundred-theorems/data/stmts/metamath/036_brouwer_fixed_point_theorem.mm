$(
  Statement-only formalization of "Brouwer Fixed Point Theorem" from Hundred
  Theorems item 036. It states the fixed-point theorem for continuous
  self-maps of nonempty compact convex subsets of finite-dimensional real
  Euclidean space. This file contains no proof.
$)

$[ library/set.mm $]

$(
  For each positive finite dimension n, RR ^m ( 1 ... n ) is the set of
  real coordinate vectors. The finite product topology below is the standard
  Euclidean topology used by SetMM's Poincare-Miranda and cube Brouwer
  development.

  Convexity is expanded directly: for x,y in s and t in [0,1], the coordinate
  map (1-t)x + ty belongs to s. The other assumptions say that s is nonempty
  and compact, f is an ambient Euclidean self-map, its restriction to s is
  continuous as a map from s to s, and its image of s is contained in s.
  The final $a assertion is the unproved corpus statement.
$)

brouwer-fixed-point-theorem $a |- A. n e. NN A. s A. f
  (
    (
      (
        s C_ ( RR ^m ( 1 ... n ) )
        /\
        s =/= (/)
      )
      /\
      (
        (
          (
            Xt_ `
              ( ( 1 ... n ) X. { ( topGen ` ran (,) ) } )
          )
          |`t s
        )
        e. Comp
        /\
        A. x e. s A. y e. s A. t e. ( 0 [,] 1 )
          (
            k e. ( 1 ... n ) |->
              (
                ( ( 1 - t ) x. ( x ` k ) )
                +
                ( t x. ( y ` k ) )
              )
          )
          e. s
      )
      /\
      (
        (
          f : ( RR ^m ( 1 ... n ) ) --> ( RR ^m ( 1 ... n ) )
          /\
          ( f " s ) C_ s
        )
        /\
        ( f |` s ) e.
          (
            (
              (
                Xt_ `
                  ( ( 1 ... n ) X. { ( topGen ` ran (,) ) } )
              )
              |`t s
            )
            Cn
            (
              (
                Xt_ `
                  ( ( 1 ... n ) X. { ( topGen ` ran (,) ) } )
              )
              |`t s
            )
          )
      )
    )
    ->
    E. x e. s ( f ` x ) = x
  )
$.
