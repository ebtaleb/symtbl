open Typedtree
open Cmt_format

let rint_type env typ =
  Format.pp_print_string Format.str_formatter "  ";
  Printtyp.wrap_printing_env env
                   (fun () -> Printtyp.type_scheme Format.str_formatter typ);
  Format.flush_str_formatter ()

let print_stack x = String.concat ", " x

let id_to_string s =
    let open Format in
    fprintf str_formatter "%a" (Ident.print) s;
    flush_str_formatter ()

let vb_tbl = ref @@ Hashtbl.create 100
let typ_tbl = ref @@ Hashtbl.create 100
let tydecl_tbl = ref @@ Hashtbl.create 100
let sc = ref []

let while_cnt = ref 0
let mk_while_id x =
    while_cnt := !while_cnt + 1;
    Printf.sprintf "while_%d_from_%s" !while_cnt x

let strip s = if s = "" then s else List.hd @@ Str.split (Str.regexp "/") s

let capture_func_args e =

  let ident patt =
    match patt.pat_desc with
      | Tpat_var (s,_) -> id_to_string s
      (*most probably the function keyword was employed, and patt match is employed on last argument*)
      (*since the param identifier doesnt appear till the lambda pass, we will just call it param for now*)
      (*to avoid name conflict in cases of several functions employing the `function` keyword, the syntbl should be*)
      (*worse even, the match might be an alpha/parametrized data struct*)


      (*remodeled as a hashtbl of kary tree desc as follows:*)
          (*- each tree root is a ocaml module with type decls and whose childrens are ocaml functions*)
          (*- the nodes are ocaml functions with name parameters, types and whose childrens are either variables (as leaves) or other functions (as local functions)*)
          (*- the leaves are value bindings of the function parent nodes*)
      | _ -> "pm_param"
  in

  let rec h expr =
  match expr.exp_desc with
  | Texp_function (_, l, _partial) ->

    assert (List.length l > 0);
    let fn_scope = try List.hd !sc with _ -> failwith "not in a function" in
    if List.length l > 1 then Printf.printf "function keyword/partial application detected for %s\n" fn_scope else
    begin
      let case = List.hd l in

      let id = if List.length > 1 then "param" else ident case.c_lhs in

      let patt = case.c_lhs in

      Printf.printf "capturing param %s from func %s\n" id fn_scope;

      let param_loc, param_env, param_type =
          (patt.pat_loc, patt.pat_env, patt.pat_type) in

      let gen_type = print_type param_env param_type in
      Hashtbl.add !vb_tbl id (param_loc, gen_type, fn_scope);
      Hashtbl.add !typ_tbl id (param_env, param_type);
      h case.c_rhs
    end
  | _ -> () in

  h e

module IterArg = struct
  include TypedtreeIter.DefaultIteratorArgument

  let enter_expression expr =
    let curr_scope = try List.hd !sc with _ -> "toplevel" in
    match expr.exp_desc with
    | Texp_let (rf, (lvb::_), e) ->
        begin
        match lvb.vb_expr.exp_desc with
        | Texp_let (_, _, _) ->
            begin
                match lvb.vb_pat.pat_desc with
                  | Tpat_var (s,_) ->
                    let es = id_to_string s in
                    if es <> curr_scope then
                        begin
                            Printf.printf "pushing let scope %s : [%s]\n" es (print_stack !sc);
                            sc := es :: !sc
                        end
                  | _ -> ()
            end
        | _ -> ()
        end
    | Texp_for (s, _, _, _, _, _) ->
        let es = id_to_string s in
        if es <> curr_scope then
            begin
                Printf.printf "entering for loop %s : [%s]\n" es (print_stack !sc);
                sc := es :: !sc
            end
    | Texp_ifthenelse _ -> Printf.printf "enter if\n"
    | Texp_while _ -> Printf.printf "enter while\n"; let ns = mk_while_id curr_scope in sc := ns :: !sc
    | _ -> ()

  let leave_expression expr =
    match expr.exp_desc with
    | Texp_for (s, _, _, _, _, _) ->
        begin
        let es = id_to_string s in
        match !sc with
          | [] -> ()
          | hd :: tl -> if es = hd then begin Printf.printf "leaving for loop %s : [%s]\n" hd (print_stack !sc); sc := tl end
        end
    | Texp_ifthenelse _ -> Printf.printf "leave if\n"
    | Texp_while _ ->
        begin
        match !sc with
          | [] -> ()
          | hd :: tl -> begin Printf.printf "leaving while loop %s : [%s]\n" hd (print_stack !sc); sc := tl end
        end
    | _ -> ()

  let enter_binding bind =
    let ident =
      match bind.vb_pat.pat_desc with
        | Tpat_var (s,_) -> id_to_string s
        | _ -> ""
    in

    let saved_let = ref "" in
    begin
    match bind.vb_expr.exp_desc with
    | Texp_let (rf, (lvb::_), e) ->
        begin
        match bind.vb_pat.pat_desc with
          | Tpat_var (s,_) ->
            let curr_scope = try List.hd !sc with _ -> "toplevel" in
            let ns = id_to_string s in
            Printf.printf "let ent %s : [%s]\n" ns (print_stack !sc);
            if ns = curr_scope then begin Printf.printf "%s are same must remove tempor\n" ns; saved_let := ns; sc := List.tl !sc end
          | _ -> ()
        end
    | _ -> () end;

    let final_scope = try List.hd !sc with _ -> "toplevel" in

    let gen_type = print_type bind.vb_expr.exp_env bind.vb_expr.exp_type in

    if ident <> ident then begin
        Hashtbl.add !vb_tbl ident (bind.vb_expr.exp_loc, gen_type, final_scope);
        Hashtbl.add !typ_tbl (strip ident) (bind.vb_expr.exp_env, bind.vb_expr.exp_type);
        Printf.printf "processed %s : [%s]\n" ident (print_stack !sc)
    end;

    match bind.vb_pat.pat_desc with
      | Tpat_var (s,_) ->
        begin
          let ns = id_to_string s in
          match bind.vb_expr.exp_desc with
          | Texp_function _ ->
              begin
                if ns <> final_scope then begin Printf.printf "pushing func %s : [%s]\n" ns (print_stack !sc); sc := ns :: !sc end;
                capture_func_args (bind.vb_expr)
              end
          | Texp_let (rf, (lvb::_), e) ->
              begin
                  if ns = !saved_let then begin Printf.printf "%s are same must restore tempor\n" ns; saved_let := ""; sc := ns :: !sc end;
                if final_scope = "toplevel" then sc := ns :: !sc
              end
          | _ -> ()
        end
      | _ -> ()

  let leave_binding bind =
    let bstr = match bind.vb_expr.exp_desc with
    | Texp_function _ -> "func"
    | Texp_let _ -> "let"
    | _ -> "" in

    match bind.vb_expr.exp_desc with
    | Texp_function _
    | Texp_let _ ->
      begin
      match bind.vb_pat.pat_desc with
        | Tpat_var (s,_) ->
            begin
            let es = id_to_string s in
            match !sc with
              | [] -> ()
              | hd :: tl -> if es = hd then begin Printf.printf "poping %s %s : [%s]\n" bstr hd (print_stack !sc); sc := tl end
            end
        | _ -> ()
      end
    | _ -> ()

  let leave_type_declaration td =
    let ident = id_to_string td.typ_id in
    Hashtbl.add !tydecl_tbl (strip ident) td.typ_type;
    Printtyp.type_declaration td.typ_id Format.str_formatter td.typ_type;
    let s = Format.flush_str_formatter () in Printf.printf "type def %s\n" s

end

module MyIterator = TypedtreeIter.MakeIterator (IterArg)

let vb structure =
  MyIterator.iter_structure structure;
  Printf.printf "got %d vbs\n" (Hashtbl.length !vb_tbl);
  Hashtbl.iter (fun k (tl,ty,scope) ->  Printf.printf "%s : %s with scope inside %s\n" k ty scope) !vb_tbl;
  Printf.printf "got %d ids and typ\n" (Hashtbl.length !typ_tbl);
  Printf.printf "got %d tyd\n" (Hashtbl.length !tydecl_tbl)

let _ =
    let fn = Sys.argv.(1) in
    let str = Cmt_format.read_cmt fn in
    match str.cmt_annots with
      | Implementation s -> vb s
      | _ -> failwith "unhandled"
