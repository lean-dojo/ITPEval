$(
  Statement-only formalization of "The Friendship Theorem" from the
  Hundred Theorems corpus, artifact 083: every finite nonempty simple
  undirected graph in which each pair of distinct vertices has exactly one
  common neighbor has a vertex adjacent to every other vertex.  This file
  contains no proof.
$)

$[ library/set.mm $]

$(
  The vertex set ` V ` is an arbitrary finite nonempty set, and adjacency is
  represented by membership of ordered pairs in the relation ` F C_ V X. V `.
  The antecedent states irreflexivity, symmetry, and restricted unique
  existence of a common neighbor for every pair of distinct vertices.  The
  consequent states that some vertex is adjacent to every other distinct
  vertex.

  This is intentionally an unproved `$a` statement, following the corpus
  convention for statement-only Metamath artifacts.
$)

${
  $d F V u v w $.

  hundred-theorems-083-friendship $a
    |- A. V A. F
      (
        (
          (
            ( V e. Fin /\ V =/= (/) )
            /\
            (
              F C_ ( V X. V )
              /\
              (
                A. u e. V -. <. u , u >. e. F
                /\
                (
                  A. u e. V A. v e. V
                    ( <. u , v >. e. F -> <. v , u >. e. F )
                  /\
                  A. u e. V A. v e. V
                    (
                      u =/= v
                      ->
                      E! w e. V
                        ( <. u , w >. e. F /\ <. v , w >. e. F )
                    )
                )
              )
            )
          )
          ->
          E. u e. V A. v e. V
            ( v =/= u -> <. u , v >. e. F )
        )
      )
  $.
$}
