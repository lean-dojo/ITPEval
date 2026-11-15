theory putnam_2001_a5 imports Complex_Main
begin

theorem putnam_2001_a5:
  shows "\<exists>!an :: int \<times> nat.
    fst an > 0 \<and> snd an > 0 \<and>
    (fst an)^(snd an + 1) - (fst an + 1)^(snd an) = 2001"
  sorry

end
