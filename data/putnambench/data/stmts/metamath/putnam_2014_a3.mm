$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_a3: evaluation as 3/7 of the infinite product associated with
  the real recurrence a_0 = 5/2 and a_k = a_(k-1)^2 - 2. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is set.mm's class of all real-valued sequences indexed by the
  nonnegative integers. Quantification over NN states the recurrence at
  exactly the positive indices, where k - 1 remains in NN0.

  For n in NN0, 0 ..^ n is the half-open interval from 0 through n - 1.
  Therefore the maps-to expression is precisely the sequence of finite
  products used by the Lean source, including the empty product at n = 0.
  Set.mm's ~~> relation states convergence of this real sequence to the
  explicit value 3/7 given by the published problem and the Rocq source.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d a k n $.

  putnambench-putnam-2014-a3 $a |-
    A. a e. ( RR ^m NN0 )
      (
        (
          ( a ` 0 ) = ( 5 / 2 )
          /\
          A. k e. NN
            ( a ` k )
            =
            ( ( ( a ` ( k - 1 ) ) ^ 2 ) - 2 )
        )
        ->
        (
          n e. NN0 |->
            prod_ k e. ( 0 ..^ n )
              ( 1 - ( 1 / ( a ` k ) ) )
        )
        ~~>
        ( 3 / 7 )
      )
  $.
$}
