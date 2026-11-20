theory HammerDemo
  imports Main
begin

lemma reverse_append_probe: "rev (xs @ ys) = rev ys @ rev xs"
  by simp

end
