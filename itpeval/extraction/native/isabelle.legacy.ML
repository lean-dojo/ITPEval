structure ITPEval_Theory =
struct
  val loaded = Thy_Info.get_names ()
  val _ = Thy_Info.use_thy (getenv "ITPEVAL_ENTRY")
  val theories = map Thy_Info.get_theory (subtract (op =) loaded (Thy_Info.get_names ()))
  fun position space name = #pos (Name_Space.the_entry space name)
  fun fact_names thy = map #2 (Global_Theory.dest_thm_names thy)
end
