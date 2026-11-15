$(
  Statement-only formalization of PutnamBench artifact putnam_1965_b5:
  existence, under the bound 4E <= V^2, of a simple undirected graph on
  V vertices with exactly E edges and no triangle. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P is an arbitrary finite vertex set of cardinality V. The subset G of
  P X. P is the adjacency relation: irreflexivity and symmetry make it a
  simple undirected graph. Each undirected edge contributes both ordered
  pairs to G, so cardinality 2 x. E is equivalent to exactly E edges.
  The final conjunct excludes three pairwise adjacent vertices.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d E G P V a b c v w $.

  putnambench-putnam-1965-b5 $a |- A. V e. NN0
    A. E e. NN0
      A. P e. Fin
        (
          (
            ( # ` P ) = V
            /\
            ( 4 x. E ) <_ ( V ^ 2 )
          )
          ->
          E. G e. ~P ( P X. P )
            (
              (
                A. v e. P -. <. v , v >. e. G
                /\
                A. v e. P A. w e. P
                  (
                    <. v , w >. e. G
                    <->
                    <. w , v >. e. G
                  )
              )
              /\
              (
                ( # ` G ) = ( 2 x. E )
                /\
                -. E. a e. P E. b e. P E. c e. P
                  (
                    <. a , b >. e. G
                    /\
                    (
                      <. a , c >. e. G
                      /\
                      <. b , c >. e. G
                    )
                  )
              )
            )
        )
  $.
$}
