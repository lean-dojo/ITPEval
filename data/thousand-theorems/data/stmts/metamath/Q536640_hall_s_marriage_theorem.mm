$(
  Statement-only formalization of Thousand Theorems corpus artifact Q536640
  (thousand-theorems__metamath__Q536640), "Hall's marriage theorem": an
  arbitrary family of finite sets has an injective system of representatives
  if and only if every finite subfamily has a union at least as large as its
  index set. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary Lean types are represented by sets I and A, and
  T : I --> ( ~P A i^i Fin ) says exactly that T is an I-indexed family of
  finite subsets of A. For a finite S C_ I, U. ( T " S ) is the union of the
  corresponding subfamily. The conclusion asks for an injective function f
  from I to A whose value at each x belongs to T(x).

  The following declaration is the single unproved $a corpus statement; this
  root statement file contains no $p proof statement.
$)

${
  $d A I S T f x $.

  thousand-theorems-q536640-hall-marriage $a |- (
    A. I e. _V A. A e. _V A. T
      (
        T : I --> ( ~P A i^i Fin )
        ->
        (
          A. S e. ( ~P I i^i Fin )
            ( # ` S ) <_ ( # ` U. ( T " S ) )
          <->
          E. f
            (
              f : I -1-1-> A
              /\
              A. x e. I ( f ` x ) e. ( T ` x )
            )
        )
      )
  ) $.
$}
