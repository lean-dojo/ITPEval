$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_b6: existence of an independent perfect dominating set in
  every specified finite-dimensional integer lattice, characterized by an
  opaque set of natural dimensions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, 0 ..^ n is the n-element ordinal corresponding to Fin n,
  and ZZ ^m ( 0 ..^ n ) is the full integer lattice of all functions from
  that carrier to ZZ. P19B6Neighbors n p q expands the source neighbor
  relation: p and q differ by absolute value one at one coordinate and
  agree at every other coordinate.

  The existential S remains an arbitrary subset of the full lattice. Its
  first property excludes every neighbor of each member, and its second
  property uses the restricted unique existential to require exactly one
  neighbor in S for each lattice point outside S. Eliminating the source
  neighbors parameter by its defining biconditional is definitionally
  equivalent to the supplied statements.

  The right side uses NN, the set of positive integers, which is the resolved
  solution recorded by the Lean annotation and explicit Rocq formalization.
  All declarations are unproved $a syntax, definition, or corpus-statement
  encodings; this database contains no $p proof declaration.
$)

$c P19B6Neighbors $.

p19b6-neighbors-syntax $a wff ( P19B6Neighbors n p q ) $.

${
  $d i j n p q $.

  p19b6-neighbors-definition $a |- (
    ( P19B6Neighbors n p q )
    <->
    E. i e. ( 0 ..^ n )
      (
        ( abs ` ( ( p ` i ) - ( q ` i ) ) ) = 1
        /\
        A. j e. ( 0 ..^ n )
          (
            j =/= i
            ->
            ( p ` j ) = ( q ` j )
          )
      )
  ) $.
$}

${
  $d n p q s $.

  putnambench-putnam-2019-b6 $a |- A. n e. NN0
    (
      (
        1 <_ n
        /\
        E. s e. ~P ( ZZ ^m ( 0 ..^ n ) )
          (
            A. p e. s
              A. q e. ( ZZ ^m ( 0 ..^ n ) )
                (
                  ( P19B6Neighbors n p q )
                  ->
                  -. q e. s
                )
            /\
            A. p e. ( ZZ ^m ( 0 ..^ n ) )
              (
                -. p e. s
                ->
                E! q e. s
                  ( P19B6Neighbors n p q )
              )
          )
      )
      <->
      n e. NN
    )
  $.
$}
