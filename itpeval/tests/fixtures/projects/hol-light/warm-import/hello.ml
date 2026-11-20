let itpeval_project_dir =
  match Sys.getenv_opt "ITPEVAL_TASK_DIR" with
  | Some path -> path
  | None -> Sys.getcwd ();;
needs (Filename.concat itpeval_project_dir "helper.ml");;
let itpeval_target = prove (`p ==> p`, ACCEPT_TAC itpeval_identity);;
