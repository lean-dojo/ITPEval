$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1188392
  (thousand-theorems__metamath__Q1188392), "Zeckendorf's theorem": the
  Fibonacci-sum map is a bijection from finite words of pairwise
  non-consecutive indices at least two to the nonnegative integers. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A Lean list is represented by a SetMM word, hence by a function on a
  half-open finite ordinal. Q1188392Reps contains exactly the words w over
  NN0 whose entries are at least two and whose adjacent entries, in list
  order, decrease by at least two. This is equivalent to
  List.IsZeckendorfRep w, including the empty word.

  Q1188392Value sends such a word to the sum of Fibci at its entries. The
  final bijection states both existence and uniqueness of a Zeckendorf
  representation for every natural number and is the inverse-direction form
  of Nat.zeckendorfEquiv.

  The final declaration is the single unproved corpus $a statement. The
  preceding $a declarations are syntax and faithful definitions only. This
  file introduces no $p proof statement.
$)

$c Q1188392Reps Q1188392Value $.

q1188392-reps-syntax $a class Q1188392Reps $.
q1188392-value-syntax $a class Q1188392Value $.

${
  $d i w $.

  q1188392-reps-definition $a |- Q1188392Reps =
    { w e. Word NN0 |
      (
        A. i e. ( 0 ..^ ( # ` w ) ) 2 <_ ( w ` i )
        /\
        A. i e. ( 1 ..^ ( # ` w ) )
          ( ( ( w ` i ) + 2 ) <_ ( w ` ( i - 1 ) ) )
      )
    }
  $.

  q1188392-value-definition $a |- Q1188392Value =
    ( w e. Q1188392Reps |->
      sum_ i e. ( 0 ..^ ( # ` w ) ) ( Fibci ` ( w ` i ) )
    )
  $.
$}

thousand-theorems-q1188392-zeckendorf $a |-
  Q1188392Value : Q1188392Reps -1-1-onto-> NN0
$.
