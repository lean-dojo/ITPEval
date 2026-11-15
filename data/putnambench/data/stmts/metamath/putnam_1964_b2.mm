$(
  Statement-only formalization of PutnamBench artifact putnam_1964_b2:
  a maximal pairwise-intersecting family of subsets of a nonempty finite set
  contains exactly half of all subsets of that set. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  S ranges over nonempty finite sets, and P ranges over families of subsets
  of S. The first quantified condition says every two members of P intersect.
  The second says that no further subset of S can be added while retaining
  that property. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d P S T U $.

  putnambench-putnam-1964-b2 $a |- A. S e. Fin
    A. P e. ~P ( ~P S )
      (
        (
          S =/= (/)
          /\
          (
            (
              A. T e. P A. U e. P
                ( T i^i U ) =/= (/)
            )
            /\
            -. E. T e. ( ( ~P S ) \ P )
              A. U e. P ( T i^i U ) =/= (/)
          )
        )
        ->
        ( # ` P ) = ( 2 ^ ( ( # ` S ) - 1 ) )
      )
  $.
$}
