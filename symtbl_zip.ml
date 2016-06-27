open Typedtree
open Cmt_format
open Zipper

open Printf

type type_and_env = Env.t * Types.type_expr
type vbind_tbl = (string, type_and_env) Hashtbl.t

type module_info =
    { type_decls : (string * Types.type_declaration) list;
      mod_name : string;}

type function_info =
    { fun_type : type_and_env;
      fun_name : string;
      fun_args : (string * Env.t * Types.type_expr) list; 
    }

type value_bind_info =
    { vb_type : type_and_env;
      vb_name : string;}

type sym_info = 
    Module of module_info 
    | Function of function_info 
    | ValueBind of value_bind_info 
    | For | While | Let

let print_type (env,typ) =
  Format.pp_print_string Format.str_formatter "  ";
  Printtyp.wrap_printing_env env
        (fun () -> Printtyp.type_scheme Format.str_formatter typ);
  Format.flush_str_formatter ()

let print_stack x = String.concat ", " x

let id_to_string s =
    let open Format in
    fprintf str_formatter "%a" (Ident.print) s;
    flush_str_formatter ()

let create_module n = leaf @@ Module {mod_name=n; type_decls=[]}
let create_vb n e t = leaf @@ ValueBind {vb_name=n; vb_type=e,t}
let create_fun n e t a = leaf @@ Function {fun_name=n; fun_type=e,t; fun_args=a}
let make_for = leaf @@ For
let make_wh = leaf @@ While
let make_let = leaf @@ Let

let sc = ref []
let tds = ref []

let root n = (create_module n, Top : sym_info zipper)
let curr_node = ref @@ root ""

let while_cnt = ref 0
let mk_while_id x =
    while_cnt := !while_cnt + 1;
    Printf.sprintf "while_%d_from_%s" !while_cnt x

let strip s = if s = "" then s else List.hd @@ Str.split (Str.regexp "/") s

let capture_func_args e =

  let ident patt case_len =
    match patt.pat_desc with
      | Tpat_var (s,_) -> assert (case_len = 1); id_to_string s
      | _ -> assert (case_len > 1); "param"
  in

  let rec h expr acc =
  match expr.exp_desc with
  | Texp_function (_, l, _partial) ->

    assert (List.length l > 0);
    begin
      let case = List.hd l in
      let id = ident case.c_lhs (List.length l) in
      let patt = case.c_lhs in

      let param_env, param_type =
          (patt.pat_env, patt.pat_type) in

      h case.c_rhs (fun ys -> acc ((id, param_env, param_type)::ys))
    end
  | _ -> acc [] in

  h e (fun ys -> ys)

module IterArg = struct
  include TypedtreeIter.DefaultIteratorArgument

  let enter_expression expr =
    let curr_scope = try List.hd !sc with _ -> "toplevel" in
    match expr.exp_desc with
    (*| Texp_let (rf, (lvb::_), e) ->*)
      (*begin*)
      (*match lvb.vb_expr.exp_desc with*)
      (*| Texp_let (_, _, _) ->*)
        (*begin*)
          (*match lvb.vb_pat.pat_desc with*)
            (*| Tpat_var (s,_) ->*)
              (*let es = id_to_string s in*)
              (*if es <> curr_scope then*)
                (*begin*)
                  (*Printf.printf "pushing let scope %s : [%s]\n" es (print_stack !sc);*)
                  (*sc := es :: !sc;*)
                  (*let upd = move_down @@ insert_down !curr_node (make_let) in curr_node := upd*)
                (*end*)
            (*| _ -> ()*)
        (*end*)
      (*| _ -> ()*)
      (*end*)
    | Texp_for (s, _, _, _, _, _) ->
      let es = id_to_string s in
      if es <> curr_scope then
          begin
              Printf.printf "entering for loop %s : [%s]\n" es (print_stack !sc);
              sc := es :: !sc;
              let upd = move_down @@ insert_down !curr_node (make_for) in curr_node := upd
          end
    | Texp_while _ -> 
        Printf.printf "enter while\n";
        let ns = mk_while_id curr_scope in sc := ns :: !sc;
        let upd = move_down @@ insert_down !curr_node (make_wh) in curr_node := upd
    | _ -> ()

  let leave_expression expr =
    match expr.exp_desc with
    | Texp_for (s, _, _, _, _, _) ->
        begin
        let es = id_to_string s in
        match !sc with
          | [] -> ()
          | hd :: tl -> 
            if es = hd then 
            begin 
              Printf.printf "leaving for loop %s : [%s]\n" hd (print_stack !sc); sc := tl;
              let upd = move_up !curr_node in curr_node := upd
            end
        end
    | Texp_while _ ->
        begin
        match !sc with
          | [] -> ()
          | hd :: tl -> 
            begin 
              Printf.printf "leaving while loop %s : [%s]\n" hd (print_stack !sc);
              sc := tl;
              let upd = move_up !curr_node in curr_node := upd
            end
        end
    | _ -> ()

  let enter_binding bind =
    let ident =
      match bind.vb_pat.pat_desc with
        | Tpat_var (s,_) -> id_to_string s
        | _ -> ""
    in

    (*let saved_let = ref "" in*)
    (*begin*)
    (*match bind.vb_expr.exp_desc with*)
    (*| Texp_let (rf, (lvb::_), e) ->*)
        (*begin*)
        (*match bind.vb_pat.pat_desc with*)
          (*| Tpat_var (s,_) ->*)
            (*let curr_scope = try List.hd !sc with _ -> "toplevel" in*)
            (*let ns = id_to_string s in*)
            (*Printf.printf "let ent %s : [%s]\n" ns (print_stack !sc);*)
            (*if ns = curr_scope then begin Printf.printf "%s are same must remove tempor\n" ns; saved_let := ns; sc := List.tl !sc end*)
          (*| _ -> ()*)
        (*end*)
    (*| _ -> () end;*)

    let final_scope = try List.hd !sc with _ -> "toplevel" in

    if ident <> "" then begin
      let vb = create_vb ident bind.vb_expr.exp_env bind.vb_expr.exp_type in
      let upd = insert_down !curr_node vb in curr_node := upd;
      Printf.printf "processed %s : [%s]\n" ident (print_stack !sc)
    end;

    match bind.vb_pat.pat_desc with
      | Tpat_var (s,_) ->
        begin
          let ns = id_to_string s in
          match bind.vb_expr.exp_desc with
          | Texp_function _ ->
            begin
              if ns <> final_scope then 
              begin 
                Printf.printf "pushing func %s : [%s]\n" ns (print_stack !sc);
                sc := ns :: !sc;
                let args = capture_func_args (bind.vb_expr) in 
                Printf.printf "got %d args\n" (List.length args);
                let funn = create_fun ns bind.vb_expr.exp_env bind.vb_expr.exp_type args in
                let upd = move_down @@ insert_down !curr_node funn in curr_node := upd;
              end
            end
          (*| Texp_let (rf, (lvb::_), e) ->*)
              (*begin*)
                  (*if ns = !saved_let then begin Printf.printf "%s are same must restore tempor\n" ns; saved_let := ""; sc := ns :: !sc end;*)
                (*if final_scope = "toplevel" then sc := ns :: !sc*)
              (*end*)
          | _ -> ()
        end
      | _ -> ()

  let leave_binding bind =
    let bstr = match bind.vb_expr.exp_desc with
    | Texp_function _ -> "func"
    (*| Texp_let _ -> "let"*)
    | _ -> "" in

    match bind.vb_expr.exp_desc with
    | Texp_function _ ->
    (*| Texp_let _ ->*)
      begin
      match bind.vb_pat.pat_desc with
        | Tpat_var (s,_) ->
          begin
          let es = id_to_string s in
          match !sc with
            | [] -> ()
            | hd :: tl ->
              if es = hd then 
              begin 
                Printf.printf "poping %s %s : [%s]\n" bstr hd (print_stack !sc); sc := tl;
                let upd = move_up !curr_node in curr_node := upd
              end
          end
        | _ -> ()
      end
    | _ -> ()

  let leave_type_declaration td =
    let ident = id_to_string td.typ_id in
    tds := !tds @ [ident, td.typ_type];

    Printtyp.type_declaration td.typ_id Format.str_formatter td.typ_type;
    let s = Format.flush_str_formatter () in Printf.printf "type def %s\n" s

end

module MyIterator = TypedtreeIter.MakeIterator (IterArg)


let change s =
  Str.replace_first (Str.regexp "/") "_" s

let dump_dot t n =

  let print x =
      let s = match x with
      | Module mi -> 
            "MOD"^mi.mod_name
      | Function fi -> 
              "FUN"^fi.fun_name
      | ValueBind vb ->
              "VB"^vb.vb_name
      | For -> "FOR"
      | While -> "WHILE"
      | _ -> "" in change s in

  let rec trav t =
    match t with
      | Branch(x, []) ->
            [sprintf "    %s;\n" (print x)]
      | Branch(x, cs) ->
          List.map
          (fun c ->
            match c with Branch(cc,_) ->
            sprintf "    %s -> %s;\n" (print x) (print cc)
          ) cs
          @ List.concat @@ List.map trav cs in

  let oc = open_out (n ^ ".dot") in
  fprintf oc "digraph BST {\n";
  fprintf oc "    nodesep=0.4;\n";
  fprintf oc "    ranksep=0.5;\n";
  fprintf oc "    node [fontname=\"Arial\"];\n";

  List.iter (output_string oc) (trav t);
  fprintf oc "}\n"; close_out oc

let sym_printer indent t =
  let is_in x = 
    match x with
      | Module mi -> sprintf "ins mod %s " mi.mod_name
      | Function fi -> sprintf "ins func %s" fi.fun_name
      | ValueBind vb -> sprintf "ins vb %s " vb.vb_name
      | _ -> "nope " in

  let print x =
      let s = match x with
      | Module mi -> 
        sprintf "mod %s\n" mi.mod_name
      | Function fi -> 
        let s = sprintf "func %s : %s\n" fi.fun_name (print_type fi.fun_type) in
        let args = List.fold_left (fun ass (n, e, t) -> ass ^ (sprintf "  %s : %s\n" n (print_type (e,t)))) "" fi.fun_args in
            s ^  "args are : " ^ args
      | ValueBind vb ->
          sprintf "vb %s : %s\n" vb.vb_name (print_type vb.vb_type)
      | For -> sprintf "inside for\n"
      | While -> sprintf "inside while\n"
      | _ -> "" in change s in

  let rec trav t =
    match t with

      | Branch(x, cs) ->
          List.map
          (fun c ->
            match c with Branch(cc,_) ->
            (is_in x) ^ (print cc)
          ) cs
          @ List.concat @@ List.map trav cs in
  trav t

let vb structure name =
  let mod_name =
    let it = List.hd structure.str_items in
    let s = it.str_loc.loc_start.pos_fname in
    Filename.chop_extension @@ String.capitalize s in
  curr_node := root mod_name;
  MyIterator.iter_structure structure;
  let res = match !curr_node with 
    | (final, Top) -> 
      begin
        match final with
        | Branch (v, cs) -> 
          match v with 
            | Module mi -> Branch (Module {mi with type_decls = !tds}, cs)
            | _ -> final
      end
    | _ -> failwith "problem with tree building" in

  sc := [];
  tds := [];
  curr_node := root "";
  let ls = sym_printer 0 res in
  List.map (print_endline) ls;
  dump_dot res mod_name

let _ =
    let fn = Sys.argv.(1) in
    let str = Cmt_format.read_cmt fn in
    match str.cmt_annots with
      | Implementation s -> vb s ""
      | _ -> failwith "unhandled"
