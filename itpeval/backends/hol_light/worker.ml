(* The worker parent loads only this coordinator and the pinned HOL core.
   Each child receives a private workspace and closes the control socket. *)

let send channel message =
  output_string channel (message ^ "\n"); flush channel

let decode_path encoded =
  let n = String.length encoded in
  if n = 0 || n mod 2 <> 0 then invalid_arg "worker path";
  String.init (n / 2) (fun i ->
    Char.chr (int_of_string ("0x" ^ String.sub encoded (2 * i) 2)))

let redirect from to_ flags =
  let fd = Unix.openfile from flags 0o600 in
  Unix.dup2 fd to_;
  Unix.close fd

let run_child control_in control_out work =
  close_in_noerr control_in;
  close_out_noerr control_out;
  try
    ignore (Unix.setsid ());
    let path name = Filename.concat work name in
    let new_log = [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL] in
    redirect "/dev/null" Unix.stdin [Unix.O_RDONLY];
    redirect (path "stdout") Unix.stdout new_log;
    redirect (path "stderr") Unix.stderr new_log;
    Unix.putenv "ITPEVAL_PROJECT" (path "project");
    Unix.putenv "ITPEVAL_TRACE" (path "trace");
    Unix.putenv "ITPEVAL_ENTRY" "hello.ml";
    let ok = Toploop.use_file Format.std_formatter (path "run.ml") in
    flush_all ();
    exit (if ok then 0 else 1)
  with exn ->
    prerr_endline (Printexc.to_string exn);
    flush_all ();
    exit 1

let rec wait pid =
  try snd (Unix.waitpid [] pid) with Unix.Unix_error (Unix.EINTR, _, _) -> wait pid

let serve () =
  let descriptor = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.set_close_on_exec descriptor;
  Unix.connect descriptor (Unix.ADDR_UNIX (Sys.getenv "ITPEVAL_HOL_WORKER_SOCKET"));
  let control_in = Unix.in_channel_of_descr (Unix.dup descriptor) in
  let control_out = Unix.out_channel_of_descr descriptor in
  send control_out (Printf.sprintf "READY %d" (Unix.getpid ()));
  let rec loop () =
    match input_line control_in with
    | exception End_of_file -> ()
    | "STOP" -> ()
    | request when String.starts_with ~prefix:"RUN " request ->
        let work = decode_path (String.sub request 4 (String.length request - 4)) in
        flush_all ();
        (match Unix.fork () with
         | 0 -> run_child control_in control_out work
         | pid ->
             (match wait pid with
              | Unix.WEXITED code -> send control_out (Printf.sprintf "EXIT %d" code)
              | Unix.WSIGNALED code | Unix.WSTOPPED code ->
                  send control_out (Printf.sprintf "SIGNAL %d" code));
             loop ())
    | _ -> invalid_arg "HOL Light worker request"
  in
  Fun.protect ~finally:(fun () -> close_in_noerr control_in; close_out_noerr control_out) loop

let () = serve ()
