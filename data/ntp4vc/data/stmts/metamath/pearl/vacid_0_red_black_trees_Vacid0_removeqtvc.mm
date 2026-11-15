$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_Vacid0_removeqtvc: the remove verification
  condition for an integer-keyed red-black-tree map with a default value,
  retaining its invariant and conditional abstract-membership equation for
  every candidate result tree. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCRed and NTP4VCBlack are the two source colors. T is exactly the
  source inductive carrier of finite integer-labelled binary trees:
  NTP4VCLeaf and NTP4VCNode are disjoint injective tagged constructors, while
  closure, exhaustiveness, and structural induction exclude missing finite
  trees and extraneous non-well-founded values.

  M, L, G, H, I, and J represent memt, lt_tree, gt_tree, bst, is_not_red,
  and rbtree. Their equations below are the complete source definitions over
  T and the full integer domain ZZ. Thus the scoped relations are uniquely
  determined by structural recursion and introduce no premise beyond the
  source definitions.

  The source pair (m,m1) is represented directly by its integer default A
  and tree B. Expanding inv makes fact0 the conjunction that B is a binary
  search tree and has an internally existentially quantified integer black
  height. For each candidate result tree t, expanding inv and mem gives the
  source predicate that t is invariant and that its abstract membership is
  the conditional key update at C relative to B. The proposition-valued
  conditional is rendered by the equivalent equality and inequality guarded
  branches. Every candidate-tree, key, value, absence-value, and black-height
  quantifier retains its source scope.

  The source conclusion is retained literally as inv (A,B) conjoined with
  the universal implication from that candidate-result predicate to itself;
  the repeated antecedent and consequent are not simplified away.

  Splitting the typed parameters, recursive definitions, and source
  assumption into scoped essential hypotheses is the curried Metamath
  sequent corresponding to the Why3 verification condition. The final $a
  declaration is Metamath's native unproved statement encoding; every
  preceding $a is syntax or a faithful definition, and this database
  contains no $p declaration.
$)

$c
  NTP4VCRed NTP4VCBlack NTP4VCColor
  NTP4VCLeaf NTP4VCNode
$.

ntp4vc-red-syntax $a class NTP4VCRed $.
ntp4vc-black-syntax $a class NTP4VCBlack $.
ntp4vc-color-syntax $a class NTP4VCColor $.
ntp4vc-leaf-syntax $a class NTP4VCLeaf $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C D E ) $.

ntp4vc-red-def $a |- NTP4VCRed = 0 $.
ntp4vc-black-def $a |- NTP4VCBlack = 1 $.
ntp4vc-color-def $a |- NTP4VCColor = { NTP4VCRed , NTP4VCBlack } $.
ntp4vc-leaf-def $a |- NTP4VCLeaf = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C D E ) =
  <. 1 , <. A , <. B , <. C , <. D , E >. >. >. >. >. $.

${
  $d a b c l n r s t u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite source color and tree datatypes. $)
  ntp4vc-tree-leaf-closure $e |- NTP4VCLeaf e. T $.

  ntp4vc-tree-node-closure $e |- A. c e. NTP4VCColor
    A. l e. T A. x e. ZZ A. y e. ZZ A. r e. T
      ( NTP4VCNode c l x y r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCLeaf
      \/
      E. c e. NTP4VCColor E. l e. T E. x e. ZZ
        E. y e. ZZ E. r e. T
          t = ( NTP4VCNode c l x y r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCLeaf e. s
        /\
        A. c e. NTP4VCColor A. l e. T A. x e. ZZ
          A. y e. ZZ A. r e. T
            (
              (
                l e. s
                /\
                r e. s
              )
              ->
              ( NTP4VCNode c l x y r ) e. s
            )
      )
      ->
      s = T
    ) $.

  $( Types of the six source recursive predicates. $)
  ntp4vc-memt-relation $e |- M C_ ( T X. ( ZZ X. ZZ ) ) $.
  ntp4vc-lt-tree-relation $e |- L C_ ( ZZ X. T ) $.
  ntp4vc-gt-tree-relation $e |- G C_ ( ZZ X. T ) $.
  ntp4vc-bst-predicate $e |- H C_ T $.
  ntp4vc-is-not-red-predicate $e |- I C_ T $.
  ntp4vc-rbtree-relation $e |- J C_ ( ZZ X. T ) $.

  $( Complete recursive definition of key-value membership. $)
  ntp4vc-memt-leaf $e |- A. x e. ZZ A. y e. ZZ
    -. <. NTP4VCLeaf , <. x , y >. >. e. M $.

  ntp4vc-memt-node $e |- A. c e. NTP4VCColor
    A. l e. T A. x e. ZZ A. y e. ZZ A. r e. T
      A. z e. ZZ A. w e. ZZ
        (
          <.
            ( NTP4VCNode c l x y r ) ,
            <. z , w >.
          >. e. M
          <->
          (
            (
              z = x
              /\
              w = y
            )
            \/
            (
              <. l , <. z , w >. >. e. M
              \/
              <. r , <. z , w >. >. e. M
            )
          )
        ) $.

  $( Exact definitions of strict key bounds. $)
  ntp4vc-lt-tree-def $e |- A. x e. ZZ A. t e. T
    (
      <. x , t >. e. L
      <->
      A. y e. ZZ A. z e. ZZ
        (
          <. t , <. y , z >. >. e. M
          ->
          y < x
        )
    ) $.

  ntp4vc-gt-tree-def $e |- A. x e. ZZ A. t e. T
    (
      <. x , t >. e. G
      <->
      A. y e. ZZ A. z e. ZZ
        (
          <. t , <. y , z >. >. e. M
          ->
          x < y
        )
    ) $.

  $( Complete recursive definition of the binary-search invariant. $)
  ntp4vc-bst-leaf $e |- NTP4VCLeaf e. H $.

  ntp4vc-bst-node $e |- A. c e. NTP4VCColor
    A. l e. T A. x e. ZZ A. y e. ZZ A. r e. T
      (
        ( NTP4VCNode c l x y r ) e. H
        <->
        (
          l e. H
          /\
          (
            r e. H
            /\
            (
              <. x , l >. e. L
              /\
              <. x , r >. e. G
            )
          )
        )
      ) $.

  $( Complete definition of non-red roots. $)
  ntp4vc-is-not-red-leaf $e |- NTP4VCLeaf e. I $.

  ntp4vc-is-not-red-red-node $e |- A. l e. T
    A. x e. ZZ A. y e. ZZ A. r e. T
      -. ( NTP4VCNode NTP4VCRed l x y r ) e. I $.

  ntp4vc-is-not-red-black-node $e |- A. l e. T
    A. x e. ZZ A. y e. ZZ A. r e. T
      ( NTP4VCNode NTP4VCBlack l x y r ) e. I $.

  $( Complete recursive red-black-tree definition with integer black height. $)
  ntp4vc-rbtree-leaf $e |- A. n e. ZZ
    (
      <. n , NTP4VCLeaf >. e. J
      <->
      n = 0
    ) $.

  ntp4vc-rbtree-red-node $e |- A. n e. ZZ A. l e. T
    A. x e. ZZ A. y e. ZZ A. r e. T
      (
        <.
          n ,
          ( NTP4VCNode NTP4VCRed l x y r )
        >. e. J
        <->
        (
          <. n , l >. e. J
          /\
          (
            <. n , r >. e. J
            /\
            (
              l e. I
              /\
              r e. I
            )
          )
        )
      ) $.

  ntp4vc-rbtree-black-node $e |- A. n e. ZZ A. l e. T
    A. x e. ZZ A. y e. ZZ A. r e. T
      (
        <.
          n ,
          ( NTP4VCNode NTP4VCBlack l x y r )
        >. e. J
        <->
        (
          <. ( n - 1 ) , l >. e. J
          /\
          <. ( n - 1 ) , r >. e. J
        )
      ) $.

  $( Source theorem parameters A=m, B=m1, C=k, followed by fact0. $)
  ntp4vc-m-integer $e |- A e. ZZ $.
  ntp4vc-m1-tree $e |- B e. T $.
  ntp4vc-k-integer $e |- C e. ZZ $.
  ntp4vc-fact0 $e |- (
    B e. H
    /\
    E. n e. ZZ <. n , B >. e. J
  ) $.

  ntp4vc-pearl-vacid-red-black-trees-remove-vc $a |- (
    (
      B e. H
      /\
      E. n e. ZZ <. n , B >. e. J
    )
    /\
    A. t e. T
      (
        (
          (
            t e. H
            /\
            E. n e. ZZ <. n , t >. e. J
          )
          /\
          A. x e. ZZ A. y e. ZZ
            (
              (
                <. t , <. x , y >. >. e. M
                \/
                (
                  y = A
                  /\
                  A. z e. ZZ
                    -. <. t , <. x , z >. >. e. M
                )
              )
              <->
              (
                (
                  x = C
                  /\
                  y = A
                )
                \/
                (
                  -. x = C
                  /\
                  (
                    <. B , <. x , y >. >. e. M
                    \/
                    (
                      y = A
                      /\
                      A. z e. ZZ
                        -. <. B , <. x , z >. >. e. M
                    )
                  )
                )
              )
            )
        )
        ->
        (
          (
            t e. H
            /\
            E. n e. ZZ <. n , t >. e. J
          )
          /\
          A. x e. ZZ A. y e. ZZ
            (
              (
                <. t , <. x , y >. >. e. M
                \/
                (
                  y = A
                  /\
                  A. z e. ZZ
                    -. <. t , <. x , z >. >. e. M
                )
              )
              <->
              (
                (
                  x = C
                  /\
                  y = A
                )
                \/
                (
                  -. x = C
                  /\
                  (
                    <. B , <. x , y >. >. e. M
                    \/
                    (
                      y = A
                      /\
                      A. z e. ZZ
                        -. <. B , <. x , z >. >. e. M
                    )
                  )
                )
              )
            )
        )
      )
  ) $.
$}
