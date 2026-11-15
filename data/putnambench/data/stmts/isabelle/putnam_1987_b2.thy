theory putnam_1987_b2 imports Complex_Main
begin

theorem putnam_1987_b2:
  fixes r s t::nat
  assumes hsum : "r + s \<le> t"
  shows "(\<Sum>i=0..s. real (s choose i) / real (t choose (r+i))) =
    real (t+1) / (real (t+1-s) * real ((t-s) choose r))"
  sorry

end
