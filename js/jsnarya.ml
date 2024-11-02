(* This file implements a javascript version of the main "executable" that can run in a browser, to be connected to xterm.js with js_of_ocaml. *)

open Js_of_ocaml
open Core
open Parser
open Top

type result = [ `Output of string | `Started ]

module Pauser = Pauseable (struct
  type t = result

  let started = `Started
end)

(* A buffer to catch stderr, for errors during loading the "extra startup" code. *)
let errbuf = Buffer.create 70
let () = Sys_js.set_channel_flusher stderr (fun str -> Buffer.add_string errbuf str)

(* And an exception to raise and catch on such errors. *)
exception Startup_error

let interact_js : string -> result =
 fun cmd ->
  (* A buffer to catch stdout, so we can return the output to JavaScript. *)
  let buf = Buffer.create 70 in
  Sys_js.set_channel_flusher stdout (fun str -> Buffer.add_string buf str);
  Reporter.try_with
    ~emit:(fun d -> Terminal.display ~use_ansi:true ~output:stdout d)
    ~fatal:(fun d -> Terminal.display ~use_ansi:true ~output:stdout d)
    (fun () -> do_command (Command.parse_single cmd));
  Out_channel.flush stdout;
  `Output (Buffer.contents buf)

(* We interface with JavaScript by exporting an object called 'Narya' with methods. *)
let _ =
  Js.export "Narya"
    (object%js
       (* The 'start' method gets things started by setting up the configuration flags and calling the initializer function. *)
       method start ar dir intr disc startup =
         arity := ar;
         set_refls dir;
         internal := intr;
         discreteness := disc;
         inputs := Snoc (Emp, `String (Js.to_string startup));
         try
           (* The "exiter" function is called if loading the "extra startup" code yields an error.  Since js_of_ocaml doesn't implement "exit" we raise our own exception instead. *)
           (match Pauser.init ~use_ansi:true ~exiter:(fun () -> raise Startup_error) () with
           | `Started -> ()
           | `Output _ -> raise (Failure "Initialization produced output"));
           Js.null
         with Startup_error ->
           (* If executing the extra startup code raises an error, we catch that error in the error buffer and return it. *)
           Out_channel.flush stderr;
           Js.some (Js.string (Buffer.contents errbuf))

       (* To execute a new command, we continue the stored continuation and return its result. *)
       method execute cmd =
         match Pauser.next (fun () -> interact_js (Js.to_string cmd)) with
         | `Started -> raise (Failure "Unexpected initialization result")
         | `Output str -> Js.string str
    end)
