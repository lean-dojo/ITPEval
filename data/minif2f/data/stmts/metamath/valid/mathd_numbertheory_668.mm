$(
  @{
    mathd-numbertheory-668.0 @e |- Y = ( Z/nZ ` 7 ) $@
    mathd-numbertheory-668.1 @e |- I = ( invr ` Y ) $@
    mathd-numbertheory-668.2 @e |- R = ( ZZring ~QG ( ( RSpan ` ZZring ) ` { 7 } ) ) $@
    mathd-numbertheory-668.3 @e |- ( ph -> L e. NN0 ) $@
    mathd-numbertheory-668.4 @e |- ( ph -> X e. NN0 ) $@
    mathd-numbertheory-668.5 @e |- ( ph -> M e. NN0 ) $@
    mathd-numbertheory-668.6 @e |- ( ph -> ( I ` [ ( 2 + 3 ) ] R ) = [ L ] R ) $@
    mathd-numbertheory-668.7 @e |- ( ph -> ( I ` [ 2 ] R ) = [ X ] R ) $@
    mathd-numbertheory-668.8 @e |- ( ph -> ( I ` [ 3 ] R ) = [ M ] R ) $@
    @( (Contributed by Kunhao Zheng, 14-Jun-2021.) @)
    mathd-numbertheory-668 @p |- ( ph ->
      ( [ L ] R
        ( +g ` Y )
        ( ( invg ` Y ) ` ( [ X ] R ( +g ` Y ) [ M ] R ) ) )
      = [ 1 ] R ) @=
      ? @.
  @}
$)
