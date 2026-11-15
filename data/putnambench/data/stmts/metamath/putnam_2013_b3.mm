$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_b3: additive representation of a valuation on a finite
  union-and-intersection-closed family with one-element descent. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, 0 ..^ n is the n-element carrier corresponding to Fin n,
  and P ranges over families of subsets of that carrier. The hypotheses
  preserve nonemptiness of P, closure under union and intersection, and the
  internal one-element descent witness for every nonempty member.

  The function f is total from the full power set to the reals, matching the
  Lean function on all finsets of Fin n. Its empty-set value and valuation
  identity are retained verbatim. The existential function r assigns a real
  weight to each carrier element, and set.mm's finite sum gives the required
  representation on every member of P. The source solution proposition is
  annotated True, so its biconditional is rendered as this assertion itself.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d P S T f i n r $.

  putnambench-putnam-2013-b3 $a |-
    A. n e. NN0
      A. P e. ~P ( ~P ( 0 ..^ n ) )
        A. f e. ( RR ^m ( ~P ( 0 ..^ n ) ) )
          (
            (
              P =/= (/)
              /\
              (
                A. S e. P A. T e. P
                  (
                    ( S u. T ) e. P
                    /\
                    ( S i^i T ) e. P
                  )
                /\
                (
                  A. S e. P
                    (
                      S =/= (/)
                      ->
                      E. T e. P
                        (
                          T C. S
                          /\
                          ( ( # ` T ) + 1 ) = ( # ` S )
                        )
                    )
                  /\
                  (
                    ( f ` (/) ) = 0
                    /\
                    A. S e. P A. T e. P
                      (
                        f
                        `
                        ( S u. T )
                      )
                      =
                      (
                        (
                          ( f ` S )
                          +
                          ( f ` T )
                        )
                        -
                        (
                          f
                          `
                          ( S i^i T )
                        )
                      )
                  )
                )
              )
            )
            ->
            E. r e. ( RR ^m ( 0 ..^ n ) )
              A. S e. P
                ( f ` S )
                =
                (
                  sum_ i e. S
                    ( r ` i )
                )
          )
  $.
$}
