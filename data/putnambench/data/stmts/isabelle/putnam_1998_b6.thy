theory putnam_1998_b6 imports Complex_Main
begin

theorem putnam_1998_b6:
  fixes a b c :: int
  shows "\<exists>n::int. n > 0 \<and>
    (\<forall>k::int. n^3 + a * n^2 + b * n + c \<noteq> k^2)"
  sorry

end
