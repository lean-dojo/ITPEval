$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_ZipperBased_buildqtvc
  (ntp4vc__metamath__pearl/vstte12_tree_reconstruction_ZipperBased_buildqtvc):
  the VSTTE 2012 zipper-based tree-reconstruction initialization verification
  condition establishes the initial forest invariant and the success and
  failure specifications for reconstructing a finite binary tree from its
  leaf-depth word. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  T is exactly the source inductive carrier of finite binary trees.
  NTP4VCLeaf and NTP4VCNode are disjoint injective tagged constructors;
  closure, exhaustiveness, and structural induction exclude missing finite
  trees, extraneous values, and non-well-founded constructor objects.

  D is the source leaf-depth function. F is forest_depths and M is map_leaf;
  their displayed empty and cons equations are their complete recursive
  definitions on arbitrary finite words. SetMM Word ZZ and
  Word ( ZZ X. T ) are exactly the source integer lists and finite forests of
  integer/tree pairs, and NTP4VCCons is exact list cons.

  R is the source recursive greedy predicate, represented as a relation on
  triples (d,(d1,t1)); its Leaf and Node biconditionals are the complete
  recursive definition. NTP4VCG is exactly the source inductive predicate g:
  empty and singleton words satisfy it vacuously, while every adjacent forest
  pair requires greedy at the current head and recurses on the tail.
  NTP4VCOnlyLeaf is the source only_leaf predicate. NTP4VCRightInvariant
  expands the source match on the right forest and its head tree, preserving
  the internal Node witnesses and the recursive g condition.

  The source let bindings are substituted definitionally: o1 is M applied to
  the input and o2 is empty. Consequently reverse o2 ++ o1 is definitionally
  o1, so forest_depths (reverse o2 ++ o1) is written F applied to M applied
  to the input. All tree, integer, result, and finite-word quantifier domains
  and all three top-level conjuncts are unchanged.

  The final $a declaration is Metamath's native unproved statement encoding;
  every preceding $a is syntax or a faithful definition, and this database
  contains no $p proof declaration.
$)

$c
  NTP4VCLeaf NTP4VCNode NTP4VCCons
  NTP4VCG NTP4VCOnlyLeaf NTP4VCRightInvariant
$.

ntp4vc-leaf-syntax
  $a class NTP4VCLeaf $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B ) $.
ntp4vc-cons-syntax
  $a class ( NTP4VCCons A B ) $.

ntp4vc-g-syntax
  $a wff ( NTP4VCG A B ) $.
ntp4vc-only-leaf-syntax
  $a wff ( NTP4VCOnlyLeaf A ) $.
ntp4vc-right-invariant-syntax
  $a wff ( NTP4VCRightInvariant A B C D ) $.

ntp4vc-leaf-definition $a |- (
  NTP4VCLeaf
) = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-cons-definition $a |- (
  NTP4VCCons A B
) = (
  <" A "> ++ B
) $.

${
  $d d h k l q r s t x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  ntp4vc-g-definition $a |- (
    ( NTP4VCG A B )
    <->
    A. k e. ( 0 ..^ ( # ` A ) )
      (
        (
          ( k + 1 )
          <
          ( # ` A )
        )
        ->
        <.
          ( 1st ` ( A ` ( k + 1 ) ) )
          ,
          <.
            ( 1st ` ( A ` k ) )
            ,
            ( 2nd ` ( A ` k ) )
          >.
        >.
        e.
        B
      )
  ) $.

  ntp4vc-only-leaf-definition $a |- (
    ( NTP4VCOnlyLeaf A )
    <->
    A. k e. ( 0 ..^ ( # ` A ) )
      (
        2nd ` ( A ` k )
      )
      =
      NTP4VCLeaf
  ) $.

  ntp4vc-right-invariant-definition $a |- (
    ( NTP4VCRightInvariant A B C D )
    <->
    (
      A = (/)
      \/
      E. d e. ZZ E. t e. D E. q e. Word ( ZZ X. D )
        (
          A = ( NTP4VCCons <. d , t >. q )
          /\
          (
            ( NTP4VCOnlyLeaf q )
            /\
            (
              t = NTP4VCLeaf
              \/
              E. l e. D E. r e. D
                (
                  t = ( NTP4VCNode l r )
                  /\
                  (
                    NTP4VCG
                      (
                        NTP4VCCons
                          <. ( d + 1 ) , l >.
                          B
                      )
                      C
                  )
                )
            )
          )
        )
    )
  ) $.

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

  ntp4vc-depths-leaf $e |- A. h e. ZZ
    (
      D ` <. h , NTP4VCLeaf >.
    ) = <" h "> $.

  ntp4vc-depths-node $e |- A. h e. ZZ A. l e. T A. r e. T
    (
      D ` <. h , ( NTP4VCNode l r ) >.
    )
    =
    (
      (
        D ` <. ( h + 1 ) , l >.
      )
      ++
      (
        D ` <. ( h + 1 ) , r >.
      )
    ) $.

  $( Complete recursive definition of forest_depths. $)
  ntp4vc-forest-depths-function $e |-
    F e. ( ( Word ZZ ) ^m ( Word ( ZZ X. T ) ) ) $.

  ntp4vc-forest-depths-empty $e |- (
    F ` (/)
  ) = (/) $.

  ntp4vc-forest-depths-cons $e |- A. h e. ZZ A. t e. T
    A. q e. Word ( ZZ X. T )
      (
        F ` ( NTP4VCCons <. h , t >. q )
      )
      =
      (
        (
          D ` <. h , t >.
        )
        ++
        (
          F ` q
        )
      ) $.

  $( Complete recursive definition of map_leaf. $)
  ntp4vc-map-leaf-function $e |-
    M e. ( ( Word ( ZZ X. T ) ) ^m ( Word ZZ ) ) $.

  ntp4vc-map-leaf-empty $e |- (
    M ` (/)
  ) = (/) $.

  ntp4vc-map-leaf-cons $e |- A. h e. ZZ A. q e. Word ZZ
    (
      M ` ( NTP4VCCons h q )
    )
    =
    (
      NTP4VCCons
        <. h , NTP4VCLeaf >.
        ( M ` q )
    ) $.

  $( Complete recursive definition of the source greedy predicate. $)
  ntp4vc-greedy-relation $e |-
    R C_ ( ZZ X. ( ZZ X. T ) ) $.

  ntp4vc-greedy-leaf $e |- A. d e. ZZ A. h e. ZZ
    (
      <. d , <. h , NTP4VCLeaf >. >. e. R
      <->
      d =/= h
    ) $.

  ntp4vc-greedy-node $e |- A. d e. ZZ A. h e. ZZ
    A. l e. T A. r e. T
      (
        <. d , <. h , ( NTP4VCNode l r ) >. >. e. R
        <->
        (
          d =/= h
          /\
          <. d , <. ( h + 1 ) , l >. >. e. R
        )
      ) $.

  $( Arbitrary source input leaf-depth list. $)
  ntp4vc-input-word $e |- A e. Word ZZ $.

  ntp4vc-pearl-vstte12-tree-reconstruction-zipper-based-build-vc $a |- (
    (
      (
        ( NTP4VCG (/) R )
        /\
        (
          NTP4VCRightInvariant
            ( M ` A )
            (/)
            R
            T
        )
      )
      /\
      A. t e. T
        (
          (
            D ` <. 0 , t >.
          )
          =
          (
            F ` ( M ` A )
          )
          ->
          (
            D ` <. 0 , t >.
          )
          =
          A
        )
    )
    /\
    (
      (
        A. t e. T
          -.
          (
            (
              D ` <. 0 , t >.
            )
            =
            (
              F ` ( M ` A )
            )
          )
      )
      ->
      A. t e. T
        -.
        (
          (
            D ` <. 0 , t >.
          )
          =
          A
        )
    )
  ) $.
$}
