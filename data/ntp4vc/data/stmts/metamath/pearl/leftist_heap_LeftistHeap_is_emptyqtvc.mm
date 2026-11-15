$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_is_emptyqtvc: the leftist-heap emptiness
  verification condition states that the Boolean constructor test returns
  true exactly when the recursive tree size is zero. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt. T is exactly the source
  inductive carrier of finite rank-labelled binary trees. NTP4VCEmpty and
  NTP4VCNode are disjoint injective tagged constructors; closure,
  exhaustiveness, and structural induction exclude missing finite trees,
  extraneous values, and non-well-founded trees.

  S is the source integer-valued size function, with its complete base and
  constructor equations over T and the full integer domain ZZ. Booleans are
  represented exactly by the two-element carrier 2, with false = 0 and
  true = 1. The source preorder, heap predicates, minimum operation, and
  auxiliary type t do not occur in fact0, size, or the conclusion, so they
  introduce no parameter or assumption into this verification condition.

  The source match in fact0 is expanded into its exhaustive Empty and Node
  cases, with the Node fields existentially scoped inside that assumption.
  Proposition equality in the Lean and Rocq sources is rendered by its
  bidirectional logical equivalent, as made explicit by the Isabelle ground
  truth. The final $a declaration is Metamath's native unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c NTP4VCEmpty NTP4VCNode $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C D ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C D ) =
  <. 1 , <. A , <. B , <. C , D >. >. >. >. $.

${
  $d l q r s t x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source arbitrary inhabited carrier elt. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.

  $( Exact finite inductive rank-labelled binary-tree carrier over U. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      ( NTP4VCNode s l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. s e. ZZ E. l e. T E. x e. U E. r e. T
        t = ( NTP4VCNode s l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. q e. ~P T
    (
      (
        NTP4VCEmpty e. q
        /\
        A. s e. ZZ A. l e. T A. x e. U A. r e. T
          (
            (
              l e. q
              /\
              r e. q
            )
            ->
            ( NTP4VCNode s l x r ) e. q
          )
      )
      ->
      q = T
    ) $.

  $( Complete recursive definition of the source integer-valued size. $)
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.

  ntp4vc-size-empty $e |- ( S ` NTP4VCEmpty ) = 0 $.

  ntp4vc-size-node $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      (
        S ` ( NTP4VCNode s l x r )
      )
      =
      (
        ( 1 + ( S ` l ) )
        +
        ( S ` r )
      ) $.

  $( Source theorem parameters A=h and B=result, followed by fact0. $)
  ntp4vc-h-tree $e |- A e. T $.
  ntp4vc-result-boolean $e |- B e. 2 $.

  ntp4vc-fact0 $e |- (
    (
      A = NTP4VCEmpty
      /\
      B = 1
    )
    \/
    E. s e. ZZ E. l e. T E. x e. U E. r e. T
      (
        A = ( NTP4VCNode s l x r )
        /\
        B = 0
      )
  ) $.

  ntp4vc-pearl-leftist-heap-is-empty-vc $a |- (
    B = 1
    <->
    ( S ` A ) = 0
  ) $.
$}
