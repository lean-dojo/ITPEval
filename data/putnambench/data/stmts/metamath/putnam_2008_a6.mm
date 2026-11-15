$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_a6: a universal logarithmic-length sequence in every finite
  nontrivial group whose ordered subsequence products cover the group. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp supplies an arbitrary group, Base ` G is its carrier,
  Fin and # express finiteness and finite cardinality, Word ( Base ` G )
  is the class of finite carrier-valued sequences, and # ` s is the length
  of the word s. The standard real function log is the natural logarithm.

  For k e. NN0, an f in
  ( ( 0 ..^ ( # ` s ) ) ^m ( 0 ..^ k ) ) is a map from the k source
  positions into the positions of s. Requiring f to be strictly increasing
  makes s o. f exactly an ordered subsequence of s, including the empty
  subsequence when k = 0. The expression G gsum ( s o. f ) is its
  left-to-right group product. Thus the witnesses k and f remain internally
  existential for each group element, and the positive real c is chosen once
  before quantifying over all finite nontrivial groups.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d c f G g i j k s $.

  putnambench-putnam-2008-a6 $a |-
    E. c e. RR
      (
        0 < c
        /\
        A. G
          (
            (
              (
                G e. Grp
                /\
                ( Base ` G ) e. Fin
              )
              /\
              1 < ( # ` ( Base ` G ) )
            )
            ->
            E. s e. Word ( Base ` G )
              (
                ( # ` s )
                <_
                (
                  c
                  x.
                  ( log ` ( # ` ( Base ` G ) ) )
                )
                /\
                A. g e. ( Base ` G )
                  E. k e. NN0
                    E. f e.
                      (
                        ( 0 ..^ ( # ` s ) )
                        ^m
                        ( 0 ..^ k )
                      )
                      (
                        A. i e. ( 0 ..^ k )
                          A. j e. ( 0 ..^ k )
                            (
                              i < j
                              ->
                              ( f ` i ) < ( f ` j )
                            )
                        /\
                        ( G gsum ( s o. f ) ) = g
                      )
              )
          )
      )
  $.
$}
