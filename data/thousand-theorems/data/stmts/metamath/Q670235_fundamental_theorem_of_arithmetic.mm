$(
  Statement-only formalization of Thousand Theorems corpus artifact Q670235
  (thousand-theorems__metamath__Q670235), "Fundamental theorem of
  arithmetic": any finite list of natural primes whose product is n has the
  prime multiplicities of the canonical prime-factor list of n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A Lean List NN0 is represented by a SetMM word, a function on the finite
  ordinal 0 ..^ #l. The first antecedent is List.prod l = n, and the second
  says that every entry of l belongs to SetMM's standard Prime class.

  For each prime p, the cardinality in the conclusion counts the occurrences
  of p in l, while ( p pCnt n ) is the exponent of p in n. Under the
  antecedents n is nonzero, and the canonical increasing list
  Nat.primeFactorsList n contains p exactly ( p pCnt n ) times. Thus equality
  of these multiplicities for every prime is bidirectionally equivalent to
  l being a permutation of Nat.primeFactorsList n.

  The final declaration is the single unproved corpus $a statement. The file
  contains no $p proof statement.
$)

${
  $d i l n p $.

  thousand-theorems-q670235-fundamental-theorem-of-arithmetic $a
    |- A. n e. NN0 A. l e. Word NN0
         (
           (
             (
               prod_ i e. ( 0 ..^ ( # ` l ) ) ( l ` i )
             ) = n
             /\
             A. i e. ( 0 ..^ ( # ` l ) ) ( ( l ` i ) e. Prime )
           )
           ->
           A. p e. Prime
             (
               # ` { i e. ( 0 ..^ ( # ` l ) ) | ( l ` i ) = p }
             ) = ( p pCnt n )
         )
  $.
$}
