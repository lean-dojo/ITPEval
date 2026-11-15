$(
  Statement-only formalization of Thousand Theorems corpus artifact Q7432915
  (thousand-theorems__metamath__Q7432915), "Schroeder-Bernstein theorem for
  measurable spaces": measurable embeddings between arbitrary measurable
  spaces in both directions yield a measurable equivalence. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q7432915MeasurableEmbedding M N F says that F is an injection from the
  carrier of sigma-algebra M into the carrier of sigma-algebra N, that F is
  measurable, and that the image under F of every M-measurable set is
  N-measurable. This is exactly the source MeasurableEmbedding structure.

  Q7432915MeasurableEquiv M N H says that H is a bijection between the
  carriers and that both H and its converse relation are measurable. For a
  bijection the converse relation is its inverse function, so this is exactly
  the source MeasurableEquiv structure.

  The final declaration is the single unproved corpus $a statement. The two
  preceding non-syntax $a declarations are faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q7432915MeasurableEmbedding Q7432915MeasurableEquiv $.

q7432915-measurable-embedding-syntax $a wff
  ( Q7432915MeasurableEmbedding M N F ) $.
q7432915-measurable-equiv-syntax $a wff
  ( Q7432915MeasurableEquiv M N H ) $.

${
  $d A F M N $.

  q7432915-measurable-embedding-definition $a |- (
    ( Q7432915MeasurableEmbedding M N F )
    <->
    (
      F : U. M -1-1-> U. N
      /\
      (
        F e. ( M MblFnM N )
        /\
        A. A e. M ( F " A ) e. N
      )
    )
  ) $.
$}

${
  $d H M N $.

  q7432915-measurable-equiv-definition $a |- (
    ( Q7432915MeasurableEquiv M N H )
    <->
    (
      H : U. M -1-1-onto-> U. N
      /\
      (
        H e. ( M MblFnM N )
        /\
        `' H e. ( N MblFnM M )
      )
    )
  ) $.
$}

${
  $d F G H M N $.

  thousand-theorems-q7432915-schroeder-bernstein-measurable-spaces $a |-
    A. M e. U. ran sigAlgebra
      A. N e. U. ran sigAlgebra
        A. F A. G
          (
            (
              ( Q7432915MeasurableEmbedding M N F )
              /\
              ( Q7432915MeasurableEmbedding N M G )
            )
            ->
            E. H ( Q7432915MeasurableEquiv M N H )
          )
  $.
$}
