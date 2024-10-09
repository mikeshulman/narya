(* This file implements a javascript version of the main "executable" that can run in a browser, to be connected to xterm.js with js_of_ocaml. *)

open Js_of_ocaml
open Effect.Deep
open Core
open Parser
open Top

(* The tricky thing here is that Top.run_top takes a callback that is run once inside all the effect handlers and is expected to do all the interaction, whereas in this case when execution of a single interactive command is finished we have to return control to the browser.  We manage this with effects.  When our run_top callback finishes a single command, it yields control by performing the "Next" effect, passing the output of the command it just executed.  The handler for this effect doesn't immediately continue, but stores the continuation in a global variable and returns control to the browser.  Then when a new command is to be executed, the continuation is resumed with the text of that command. *)

(* We also need an extra "no output yet" flag to be returned by the first call that initializes the setup. *)
type result = [ `Output of string | `Started ]
type _ Effect.t += Next : result -> string Effect.t

(* A buffer to catch stderr, for errors during loading the "extra startup" code. *)
let errbuf = Buffer.create 70
let () = Sys_js.set_channel_flusher stderr (fun str -> Buffer.add_string errbuf str)

(* And an exception to raise and catch on such errors. *)
exception Startup_error

(* Here is the run_top callback that appears to do all the interaction itself with an infinite recursion.  It takes a command to execute as its argument.  It doesn't actually ever return, but we declare its return type to be 'result' so that it will be well-typed to match the results of the Next effects. *)
let rec interact_js : string -> result =
 fun cmd ->
  (* A buffer to catch stdout, so we can return the output to JavaScript. *)
  let buf = Buffer.create 70 in
  Sys_js.set_channel_flusher stdout (fun str -> Buffer.add_string buf str);
  Reporter.try_with
    ~emit:(fun d -> Terminal.display ~use_ansi:true ~output:stdout d)
    ~fatal:(fun d -> Terminal.display ~use_ansi:true ~output:stdout d)
    (fun () -> do_command (Command.parse_single cmd));
  Out_channel.flush stdout;
  (* Now we perform the "Next" effect, which returns control to the browser until the user enters another command.  At that point execution resumes here with a return value of the next command to execute, which we then pass off to ourselves recursively. *)
  interact_js (Effect.perform (Next (`Output (Buffer.contents buf))))

(* The stored continuation, which points into the callback inside run_top. *)
let cont : (string, result) continuation option ref = ref None

(* The effect handler that saves the continuation and returns the output passed to 'Next'. *)
let effc : type b. b Effect.t -> ((b, result) continuation -> result) option = function
  | Next output ->
      Some
        (fun k ->
          cont := Some k;
          output)
  | _ -> None

(* We initialize the setup by calling run_top inside the effect handler. *)
let init () =
  match
    try_with
      (fun () ->
        (* The "exiter" function is called if loading the "extra startup" code yields an error.  Since js_of_ocaml doesn't implement "exit" we raise our own exception instead. *)
        run_top ~use_ansi:true ~exiter:(fun () -> raise Startup_error) @@ fun () ->
        (* For the first call, there is no output to return, so we just return "Started". *)
        interact_js (Effect.perform (Next `Started)))
      () { effc }
  with
  | `Started -> ()
  | `Output _ -> raise (Failure "Initialization produced output")

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
           init ();
           Js.null
           (* If executing the extra startup code raises an error, we catch that error in the error buffer and return it. *)
         with Startup_error ->
           Out_channel.flush stderr;
           Js.some (Js.string (Buffer.contents errbuf))

       (* To execute a new command, we continue the stored continuation and return its result. *)
       method execute cmd =
         match continue (Option.get !cont) (Js.to_string cmd) with
         | `Started -> raise (Failure "Unexpected initialization result")
         | `Output str -> Js.string str
    end)
