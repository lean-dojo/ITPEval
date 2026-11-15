$(
  Statement-only formalization of Hundred Theorems item 031, the infinite
  Ramsey theorem.

  This reproduces set.mm theorem ramsey. C(a,i) is the class of i-element
  subsets of a. For every finite coloring F of M-element subsets, the
  conclusion supplies arbitrarily large homogeneous subsets.
$)

$[ library/set.mm $]

${
  $d f c n s x F $.
  $d a b c f i n s x M $.
  $d R c f n s x $.
  $d C c f x $.

  hundred-theorems-031-subsets-of-size $e
    |- C =
       ( a e. _V , i e. NN0 |->
         { b e. ~P a | ( # ` b ) = i } )
  $.

  hundred-theorems-031-ramsey $a
    |- (
         ( M e. NN0 /\ R e. Fin /\ F : R --> NN0 )
         ->
         E. n e. NN0
           A. s
             (
               n <_ ( # ` s )
               ->
               A. f e. ( R ^m ( s C M ) )
                 E. c e. R
                   E. x e. ~P s
                     (
                       ( F ` c ) <_ ( # ` x )
                       /\
                       ( x C M ) C_ ( `' f " { c } )
                     )
             )
       )
  $.
$}
