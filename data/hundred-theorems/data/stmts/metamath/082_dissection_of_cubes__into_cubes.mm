$(
  Statement-only formalization of "Dissection of Cubes (into Cubes)" from
  Hundred Theorems corpus artifact 082: in every real dimension at least
  three, a cube cannot be partitioned into finitely many nontrivial
  axis-aligned cubes having pairwise distinct positive widths. This file
  contains no proof.
$)

$[ library/set.mm $]

$(
  Coordinates are indexed by 1 ... n.  The function B assigns each member
  of the finite family its bottom coordinate vector, and W assigns its real
  width.  HT082CubePoint uses the half-open convention

    B(i)(j) <= x(j) < B(i)(j) + W(i),

  matching the Lean and Isabelle sources.  HT082UnitPoint is the analogous
  half-open unit cube.  Exact equality of the union with the unit cube is
  expressed pointwise, so no geometric content is hidden in an
  uninterpreted predicate.

  Indexing the family by 1 ... k is equivalent to the source's arbitrary
  finite set of cubes.  The injectivity of W makes the indexed cubes
  distinct and states exactly that their widths are pairwise different.
  The final declaration is an unproved $a statement.
$)

$c HT082CubePoint HT082UnitPoint $.

ht082-cube-point-syntax $a
  wff ( x HT082CubePoint n B W i )
$.

ht082-unit-point-syntax $a
  wff ( x HT082UnitPoint n )
$.

${
  $d B W i j n x $.

  ht082-cube-point-definition $a
    |- (
      ( x HT082CubePoint n B W i )
      <->
      (
        x e. ( RR ^m ( 1 ... n ) )
        /\
        A. j e. ( 1 ... n )
          (
            ( ( ( B ` i ) ` j ) <_ ( x ` j ) )
            /\
            ( ( x ` j ) < ( ( ( B ` i ) ` j ) + ( W ` i ) ) )
          )
      )
    )
  $.
$}

${
  $d j n x $.

  ht082-unit-point-definition $a
    |- (
      ( x HT082UnitPoint n )
      <->
      (
        x e. ( RR ^m ( 1 ... n ) )
        /\
        A. j e. ( 1 ... n )
          ( 0 <_ ( x ` j ) /\ ( x ` j ) < 1 )
      )
    )
  $.
$}

${
  $d B W h i k n x $.

  hundred-theorems-082-dissection-of-cubes $a
    |- -.
      E. n e. NN E. k e. NN E. B E. W
        (
          (
            ( 3 <_ n /\ 2 <_ k )
            /\
            (
              B : ( 1 ... k ) --> ( RR ^m ( 1 ... n ) )
              /\
              W : ( 1 ... k ) -1-1-> RR
            )
          )
          /\
          (
            A. i e. ( 1 ... k ) 0 < ( W ` i )
            /\
            (
              A. i e. ( 1 ... k ) A. h e. ( 1 ... k )
                (
                  i =/= h
                  ->
                  -. E. x
                    (
                      ( x HT082CubePoint n B W i )
                      /\
                      ( x HT082CubePoint n B W h )
                    )
                )
              /\
              A. x
                (
                  ( x HT082UnitPoint n )
                  <->
                  E. i e. ( 1 ... k )
                    ( x HT082CubePoint n B W i )
                )
            )
          )
        )
  $.
$}
