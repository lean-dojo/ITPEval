$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/foveoos11_cm/tree_max_TreeMax_maxqtvc: the tree-maximum verification
  condition states that a result assembled from a right-subtree upper bound
  and a left-subtree upper bound is both an upper bound and a member of the
  original nonempty integer-labelled binary tree. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  T is exactly the source inductive carrier of finite integer-labelled binary
  trees. NTP4VCEmpty and NTP4VCNode are disjoint injective tagged
  constructors; closure, exhaustiveness, and structural induction exclude
  missing finite trees, extraneous values, and non-well-founded trees.

  M and G represent the source recursive predicates mem and ge_tree.
  Their Empty and Node equations below are the complete recursive definitions
  over T and the full integer domain ZZ. Thus <. x , t >. e. M says that x is
  a label in t, while <. x , t >. e. G says that every label in t is at most
  x.

  The source matches on t are expanded with existential constructor
  components. The first match asserts that t is a Node. In the second match,
  the right-subtree bound o remains existentially quantified inside the
  antecedent for each universally quantified integer result. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c NTP4VCEmpty NTP4VCNode $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

${
  $d l o q r s t v x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite inductive binary-tree carrier over the full integers. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. v e. ZZ A. l e. T A. r e. T
    ( NTP4VCNode v l r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. v e. ZZ E. l e. T E. r e. T
        t = ( NTP4VCNode v l r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. v e. ZZ A. l e. T A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode v l r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Complete recursive source definitions of mem and ge_tree. $)
  ntp4vc-mem-relation $e |- M C_ ( ZZ X. T ) $.
  ntp4vc-ge-tree-relation $e |- G C_ ( ZZ X. T ) $.

  ntp4vc-mem-empty $e |- A. x e. ZZ
    -. <. x , NTP4VCEmpty >. e. M $.

  ntp4vc-mem-node $e |- A. x e. ZZ A. v e. ZZ
    A. l e. T A. r e. T
      (
        <. x , ( NTP4VCNode v l r ) >. e. M
        <->
        (
          x = v
          \/
          (
            <. x , l >. e. M
            \/
            <. x , r >. e. M
          )
        )
      ) $.

  ntp4vc-ge-tree-empty $e |- A. x e. ZZ
    <. x , NTP4VCEmpty >. e. G $.

  ntp4vc-ge-tree-node $e |- A. x e. ZZ A. v e. ZZ
    A. l e. T A. r e. T
      (
        <. x , ( NTP4VCNode v l r ) >. e. G
        <->
        (
          v <_ x
          /\
          (
            <. x , l >. e. G
            /\
            <. x , r >. e. G
          )
        )
      ) $.

  $( Source theorem parameter A=t and its sole assumption fact0. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-fact0 $e |- A =/= NTP4VCEmpty $.

  ntp4vc-pearl-foveoos11-cm-tree-max-tree-max-max-vc $a |- (
    (
      E. v e. ZZ E. l e. T E. r e. T
        A = ( NTP4VCNode v l r )
    )
    /\
    A. q e. ZZ
      (
        (
          E. v e. ZZ E. l e. T E. r e. T
            (
              A = ( NTP4VCNode v l r )
              /\
              E. o e. ZZ
                (
                  (
                    <. o , r >. e. G
                    /\
                    (
                      v <_ o
                      /\
                      (
                        o = v
                        \/
                        <. o , r >. e. M
                      )
                    )
                  )
                  /\
                  (
                    <. q , l >. e. G
                    /\
                    (
                      o <_ q
                      /\
                      (
                        q = o
                        \/
                        <. q , l >. e. M
                      )
                    )
                  )
                )
            )
        )
        ->
        (
          <. q , A >. e. G
          /\
          <. q , A >. e. M
        )
      )
  ) $.
$}
