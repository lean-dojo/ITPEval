$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_b2: every nonempty cancellative semigroup in which each
  element has only finitely many positive powers is a group, identified
  with the source's solution proposition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary carrier is the set s, and f is an arbitrary total binary
  operation from s X. s to s. The antecedent states nonemptiness,
  associativity, and both cancellation laws.

  For each a in s, the internally existential sequence p has p(0) = a and
  p(n+1) = f(a,p(n)). Its range is therefore exactly the set of positive
  powers of a, with the same indexing as the Lean and Isabelle sources, and
  requiring ran p to be finite preserves their finiteness hypothesis.

  The resolved answer is True, so the statement directly asserts the group
  conclusion. The identity and inverse witnesses remain inside the
  conclusion for each arbitrary semigroup. The final declaration is the
  single unproved $a corpus statement; this statement file contributes no
  $p proof statement.
$)

${
  $d a e f n p s x y z $.

  putnambench-putnam-1989-b2 $a |-
      A. s
        A. f e. ( s ^m ( s X. s ) )
          (
            (
              (
                s =/= (/)
                /\
                A. x e. s A. y e. s A. z e. s
                  ( f ` <. ( f ` <. x , y >. ) , z >. )
                  =
                  ( f ` <. x , ( f ` <. y , z >. ) >. )
              )
              /\
              A. x e. s A. y e. s A. z e. s
                (
                  (
                    ( f ` <. x , y >. ) = ( f ` <. x , z >. )
                    ->
                    y = z
                  )
                  /\
                  (
                    ( f ` <. y , x >. ) = ( f ` <. z , x >. )
                    ->
                    y = z
                  )
                )
              /\
              A. a e. s
                E. p e. ( s ^m NN0 )
                  (
                    (
                      ( p ` 0 ) = a
                      /\
                      A. n e. NN0
                        ( p ` ( n + 1 ) )
                        =
                        ( f ` <. a , ( p ` n ) >. )
                    )
                    /\
                    ran p e. Fin
                  )
            )
            ->
            E. e e. s
              A. x e. s
                (
                  (
                    ( f ` <. e , x >. ) = x
                    /\
                    ( f ` <. x , e >. ) = x
                  )
                  /\
                  E. y e. s
                    (
                      ( f ` <. x , y >. ) = e
                      /\
                      ( f ` <. y , x >. ) = e
                    )
                )
          )
  $.
$}
