$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_Harness_harnessqtvc
  (ntp4vc__metamath__pearl/vstte12_tree_reconstruction_Harness_harnessqtvc):
  the VSTTE 2012 tree-reconstruction harness verification condition states
  that the leaf-depth sequence [1, 3, 3, 2] is realized by and uniquely
  determines the specified finite binary tree when its root is at depth zero.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  T is exactly the source inductive carrier of finite binary trees.
  NTP4VCLeaf and NTP4VCNode are disjoint injective tagged constructors;
  closure, exhaustiveness, and structural induction exclude missing finite
  trees, extraneous values, and non-well-founded constructor objects.

  D is the source integer-indexed leaf-depth function into finite integer
  words. Its Leaf and Node equations are the complete recursive definition:
  a leaf contributes its current depth, while a node concatenates the depth
  words of both children at depth d + 1.

  The source let-binding for [1, 3, 3, 2] is substituted definitionally.
  The first conjunct retains the universal result scope and states that every
  tree with that depth word equals the displayed tree. The second conjunct
  retains the source negated universal and therefore states that some tree
  has that depth word. The final $a declaration is Metamath's native unproved
  statement encoding; every preceding $a is syntax or a faithful constructor
  definition, and this database contains no $p proof declaration.
$)

$c NTP4VCLeaf NTP4VCNode $.

ntp4vc-leaf-syntax $a class NTP4VCLeaf $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B ) $.

ntp4vc-leaf-definition $a |-
  NTP4VCLeaf = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B
) = <. 1 , <. A , B >. >. $.

${
  $d d l r s t x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite inductive binary-tree carrier. $)
  ntp4vc-tree-leaf-closure $e |- NTP4VCLeaf e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. r e. T
    ( NTP4VCNode l r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCLeaf
      \/
      E. l e. T E. r e. T
        t = ( NTP4VCNode l r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCLeaf e. s
        /\
        A. l e. T A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Complete recursive definition of leaf depths over all integer offsets. $)
  ntp4vc-depths-function $e |-
    D e. ( ( Word ZZ ) ^m ( ZZ X. T ) ) $.

  ntp4vc-depths-leaf $e |- A. d e. ZZ
    (
      D ` <. d , NTP4VCLeaf >.
    ) = <" d "> $.

  ntp4vc-depths-node $e |- A. d e. ZZ A. l e. T A. r e. T
    (
      D ` <. d , ( NTP4VCNode l r ) >.
    )
    =
    (
      (
        D ` <. ( d + 1 ) , l >.
      )
      ++
      (
        D ` <. ( d + 1 ) , r >.
      )
    ) $.

  ntp4vc-pearl-vstte12-tree-reconstruction-harness-harness-vc $a |- (
    A. x e. T
      (
        (
          D ` <. 0 , x >.
        )
        =
        (
          <" 1 ">
          ++
          (
            <" 3 ">
            ++
            (
              <" 3 ">
              ++
              <" 2 ">
            )
          )
        )
        ->
        x
        =
        (
          NTP4VCNode
            NTP4VCLeaf
            (
              NTP4VCNode
                ( NTP4VCNode NTP4VCLeaf NTP4VCLeaf )
                NTP4VCLeaf
            )
        )
      )
    /\
    -.
    A. t e. T
      -.
      (
        D ` <. 0 , t >.
      )
      =
      (
        <" 1 ">
        ++
        (
          <" 3 ">
          ++
          (
            <" 3 ">
            ++
            <" 2 ">
          )
        )
      )
  ) $.
$}
