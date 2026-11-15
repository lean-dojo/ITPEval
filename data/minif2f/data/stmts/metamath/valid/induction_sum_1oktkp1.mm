$(
  @{
    @d N k x $@
    @d k y x $@
    @d ph x y $@
    induction-sum-1oktkp1.0 @e |- ( ph -> N e. NN ) $@
    @( (Contributed by Stanislas Polu, 14-Oct-2020.) @)
    induction-sum-1oktkp1 @p |- ( ph -> sum_ k e. ( 1 ... N ) ( 1 / ( k x. ( k + 
  1 ) ) ) = ( N / ( N + 1 ) ) ) @=
      ? @.
  @}
$)
