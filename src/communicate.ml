open Printf
open Yojson

type message = 
    | Create_session of string * string * string * (string list)
    | Remove_session of string
    | Add_node of string * string * string * string
    | Remove_node of string * string
    | Add_edge of string * string * string * string
    | Remove_edge of string * string * string
    | Change_node_state of string * string * string
    | Highlight_node of string * string
    | Unhighlight_node of string * string
    | Clear_color of string
    | Request of string * (string list)
    | Response of string * (string list) * (string list)
    | Feedback_ok of string
    | Feedback_fail of string * string

let str_msg msg = 
    match msg with
    | Create_session (sid, session_descr, graph_type, attris) -> "Create_session ("^sid^", "^ session_descr^", "^graph_type^", "^(Lists.str_slist attris "[" "]" ",")^")"
    | Remove_session (sid) -> "Remove_session "^sid
    | Add_node (sid, nid, label, state) -> "Add_node ("^sid^", "^nid^", "^label^", "^state^")"
    | Remove_node (sid, nid) -> "Remove_node ("^sid^", "^nid^")"
    | Add_edge (sid, from_id, to_id, label) -> "Add_edge ("^sid^", "^from_id^", "^to_id^","^label^")"
    | Remove_edge (sid, from_id, to_id) -> "Remove_edge ("^sid^", "^from_id^","^to_id^")"
    | Change_node_state (sid, nid, state) -> "Change_node_state ("^sid^", "^nid^", "^state^")"
    | Highlight_node (sid, nid) -> "Highlight_node ("^sid^", "^nid^")"
    | Unhighlight_node (sid, nid) -> "Unhighlight_node ("^sid^", "^nid^")"
    | Clear_color sid -> "Clear_color "^sid
    | Request (sid, attris) -> 
        if attris = [] then
            "Request ("^sid^", [])"
        else if List.length attris = 1 then
            "Request ("^sid^", ["^(List.hd attris)^"])"
        else begin
            "Request ("^sid^", ["^(List.fold_left (fun str attri -> str^","^attri) (List.hd attris) (List.tl attris))^"])"
        end
    | Response (sid, attris, nids) -> 
        "Response ("^sid^", "^(Lists.str_slist attris "[" "]" ",")^", "^(Lists.str_slist nids "[" "]" ",")^")"
    | Feedback_ok sid -> "Feedback_ok "^sid
    | Feedback_fail (sid, error_msg) -> "Feedback_fail ("^sid^", "^error_msg^")"


(*let protocol_version_no = "20170502"*)
let sending_queue = Queue.create ()
let sending_mutex = Mutex.create ()
let sending_conditional = Condition.create ()
let log_file = "log"

let vin = ref stdin
let vout = ref stdout

let wait_to_send msg = 
    Mutex.lock sending_mutex;
    Queue.push msg sending_queue;
    Condition.signal sending_conditional;
    Mutex.unlock sending_mutex

let create_proof_session session attris = wait_to_send (Create_session (session, session, "Tree", attris))
let create_state_session session attris = wait_to_send (Create_session (session, session, "DiGraph", attris))
let remove_session sid = wait_to_send (Remove_session sid)
let add_node sid nid label state = wait_to_send (Add_node (sid, nid, label, state))
let remove_node sid nid = wait_to_send (Remove_node (sid, nid))
let add_edge sid from_id to_id label = wait_to_send (Add_edge (sid, from_id, to_id, label))
let remove_edge sid from_id to_id = wait_to_send (Remove_edge (sid, from_id, to_id))
let change_node_state sid nid state = wait_to_send (Change_node_state (sid, nid, state))
let highlight_node sid nid = wait_to_send (Highlight_node (sid, nid))
let unhighlight_node sid nid = wait_to_send (Unhighlight_node (sid, nid))
let clear_color sid = wait_to_send (Clear_color sid)
let request sid attris = wait_to_send (Request (sid, attris))
let response sid attris nids = wait_to_send (Response (sid, attris, nids))
let feedback_ok sid = wait_to_send (Feedback_ok sid)
let feedback_fail sid error_msg = wait_to_send (Feedback_fail (sid, error_msg))


let json_of_msg (msg:message) = 
    match msg with
    | Create_session (session_id, session_descr, graph_type, attris) ->
        `Assoc [
            ("type", `String "create_session");
            ("session_id", `String session_id);
            ("session_descr", `String session_descr);
            ("graph_type", `String graph_type);
            ("attributes", `List (List.map (fun attri -> `String attri) attris))
        ]
    | Remove_session sid ->
        `Assoc [
            ("type", `String "remove_session");
            ("session_id", `String sid)
        ]
    | Add_node (sid, nid, label, state) ->
        `Assoc [
            ("type", `String "add_node");
            ("session_id", `String sid);
            ("node", `Assoc [
                ("id", `String nid);
                ("label", `String (label));
                ("state", `String (state))
            ])
        ]
    | Remove_node (sid, nid) ->
        `Assoc [
            ("type", `String "remove_node");
            ("session_id", `String sid);
            ("node_id", `String nid)
        ]
    | Add_edge (sid, from_id, to_id, label) ->
        `Assoc [
            ("type", `String "add_edge");
            ("session_id", `String sid);
            ("from_id", `String from_id);
            ("to_id", `String to_id);
            ("label", `String label)
        ]
    | Remove_edge (sid, from_id, to_id) ->
        `Assoc [
            ("type", `String "remove_edge");
            ("session_id", `String sid);
            ("from_id", `String from_id);
            ("to_id", `String to_id)
        ]
    | Change_node_state (sid, nid, new_state) ->
        `Assoc [
            ("type", `String "change_node_state");
            ("session_id", `String sid);
            ("node_id", `String nid);
            ("new_state", `String (new_state))
        ]
    | Highlight_node (sid, nid) ->
        `Assoc [
            ("type", `String "highlight_node");
            ("session_id", `String sid);
            ("node_id", `String nid)
        ]
    | Unhighlight_node (sid, nid) ->
        `Assoc [
            ("type", `String "unhighlight_node");
            ("session_id", `String sid);
            ("node_id", `String nid)
        ]
    | Clear_color sid ->
        `Assoc [
            ("type", `String "clear_color");
            ("session_id", `String sid)
        ]
    | Request (sid, attris) ->
        `Assoc [
            ("type", `String "request");
            ("session_id", `String sid);
            ("attributes", `List (List.map (fun str -> `String str) attris))
        ]
    | Response (sid, attris, nids) ->
        `Assoc [
            ("type", `String "response");
            ("session_id", `String sid);
            ("attributes", `List (List.map (fun str -> `String str) attris));
            ("nodes", `List (List.map (fun str -> `String str) nids))
        ]
    | Feedback_ok sid ->
        `Assoc [
            ("type", `String "feedback");
            ("session_id", `String sid);
            ("status", `String "OK")
        ]
    | Feedback_fail (sid, error_msg) ->
        `Assoc [
            ("type", `String "feedback");
            ("session_id", `String sid);
            ("status", `String "Fail");
            ("error_msg", `String error_msg)
        ]

let rec get_json_of_key key str_json_list = 
    match str_json_list with
    | (str, json) :: str_json_list' -> 
        if str = key then
            json
        else 
            get_json_of_key key str_json_list'
    | [] -> printf "not find json for key %s\n" key; exit 1 


let get_string_of_json json = 
    match json with
    | `String str -> str
    | _ -> printf "%s is not a string\n" (Yojson.Basic.to_string json); exit 1

let get_string_list_of_json jsons = 
    match jsons with
    | `List jsons -> List.map (fun json -> get_string_of_json json) jsons 
    | _ -> printf "%s is not a list\n" (Yojson.Basic.to_string jsons); exit 1 


let msg_of_json json = 
    match json with
    | `Assoc str_json_list -> begin
            match get_string_of_json (get_json_of_key "type" str_json_list) with
            | "highlight_node" -> 
                Highlight_node ((get_string_of_json (get_json_of_key "session_id" str_json_list)), (get_string_of_json (get_json_of_key "node_id" str_json_list)))
                (*printf "highlight node %s in session %s\n" (get_string_of_json (get_json_of_key "node_id" str_json_list)) (get_string_of_json (get_json_of_key "session_id" str_json_list));
                flush stdout*)
            | "feedback" -> 
                let status = get_string_of_json (get_json_of_key "status" str_json_list) in
                if status = "OK" then
                    Feedback_ok (get_string_of_json (get_json_of_key "session_id" str_json_list))
                    (*printf "OK from session %s\n" (get_string_of_json (get_json_of_key "session_id" str_json_list))*)
                else
                    Feedback_fail ((get_string_of_json (get_json_of_key "session_id" str_json_list)), (get_string_of_json (get_json_of_key "error_msg" str_json_list)))
                    (*printf "Fail from session %s: %s\n" (get_string_of_json (get_json_of_key "session_id" str_json_list)) (get_string_of_json (get_json_of_key "error_msg" str_json_list));*)
                (*flush stdout*)

            | "unhighlight_node" ->
                Unhighlight_node ((get_string_of_json (get_json_of_key "session_id" str_json_list)), (get_string_of_json (get_json_of_key "node_id" str_json_list)))
            | "clear_color" ->
                Clear_color (get_string_of_json (get_json_of_key "session_id" str_json_list))
            | "request" ->
                Request (get_string_of_json (get_json_of_key "session_id" str_json_list), get_string_list_of_json (get_json_of_key "attributes" str_json_list))
            | "response" -> 
                Response (get_string_of_json (get_json_of_key "session_id" str_json_list), get_string_list_of_json (get_json_of_key "attributes" str_json_list), get_string_list_of_json (get_json_of_key "nodes" str_json_list))
            | _ as s -> printf "not supposed to be received by the prover: %s\n" s; exit 1
        end
    | _ -> printf "%s can not be a message\n" (Yojson.Basic.to_string json); exit 1

let sending cout =
    let running = ref true in
    let log_out = open_out log_file in
    while !running do
        if Queue.is_empty sending_queue then begin
            Mutex.lock sending_mutex;
            Condition.wait sending_conditional sending_mutex;
            Mutex.unlock sending_mutex
        end else begin
            let msg = ref (Feedback_ok "") in
            Mutex.lock sending_mutex;
            msg := Queue.pop sending_queue;
            Mutex.unlock sending_mutex;
            (*begin
                match !msg with
                | Terminate -> running := false
                | _ -> ()
            end;*)
            let json_msg = json_of_msg !msg in
            (*Yojson.Basic.to_channel cout json_msg;*)
            output_string cout ((Yojson.Basic.to_string json_msg));
            flush cout;
            output_string cout "\n";
            flush cout;
            Thread.delay (0.001);
            output_string log_out "JSON data sent:\n";
            output_string log_out (Yojson.Basic.to_string json_msg);
            output_string log_out "\n";
            flush log_out
        end
    done



let receiving cin parse = 
    let running = ref true in
    let log_out = open_out log_file in
    while !running do
        let json_str = input_line cin in
        let json_msg = Yojson.Basic.from_string json_str in
        (*let json_msg = Yojson.Basic.from_channel cin in*)
        output_string log_out "JSON data received:\n";
        output_string log_out (Yojson.Basic.to_string json_msg);
        output_string log_out "\n";
        flush log_out;
        let msg = msg_of_json json_msg in
        parse msg
    done

let start_send_receive cin cout parse =
    (*ignore (Thread.create (fun cin -> receiving cin parse) cin);*)
    ignore (Thread.create (fun cout -> sending cout) cout);
    receiving cin parse

let init ip_addr = 
    let i,o = Unix.open_connection (Unix.ADDR_INET (Unix.inet_addr_of_string ip_addr, 3333)) in
    vin := i;
    vout := o;
    i,o




