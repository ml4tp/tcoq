(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Tok
open Compat

(* Dictionaries: trees annotated with string options, each node being a map
   from chars to dictionaries (the subtrees). A trie, in other words. *)

module CharOrd = struct type t = char let compare : char -> char -> int = compare end
module CharMap = Map.Make (CharOrd)

type ttree = {
  node : string option;
  branch : ttree CharMap.t }

let empty_ttree = { node = None; branch = CharMap.empty }

let ttree_add ttree str =
  let rec insert tt i =
    if i == String.length str then
      {node = Some str; branch = tt.branch}
    else
      let c = str.[i] in
      let br =
        match try Some (CharMap.find c tt.branch) with Not_found -> None with
          | Some tt' ->
              CharMap.add c (insert tt' (i + 1)) (CharMap.remove c tt.branch)
          | None ->
              let tt' = {node = None; branch = CharMap.empty} in
              CharMap.add c (insert tt' (i + 1)) tt.branch
      in
      { node = tt.node; branch = br }
  in
  insert ttree 0

(* Search a string in a dictionary: raises [Not_found]
   if the word is not present. *)

let ttree_find ttree str =
  let rec proc_rec tt i =
    if i == String.length str then tt
    else proc_rec (CharMap.find str.[i] tt.branch) (i+1)
  in
  proc_rec ttree 0

(* Removes a string from a dictionary: returns an equal dictionary
   if the word not present. *)
let ttree_remove ttree str =
  let rec remove tt i =
    if i == String.length str then
      {node = None; branch = tt.branch}
    else
      let c = str.[i] in
      let br =
        match try Some (CharMap.find c tt.branch) with Not_found -> None with
          | Some tt' ->
              CharMap.add c (remove tt' (i + 1)) (CharMap.remove c tt.branch)
          | None -> tt.branch
      in
      { node = tt.node; branch = br }
  in
  remove ttree 0

let ttree_elements ttree =
  let rec elts tt accu =
    let accu = match tt.node with
    | None -> accu
    | Some s -> CString.Set.add s accu
    in
    CharMap.fold (fun _ tt accu -> elts tt accu) tt.branch accu
  in
  elts ttree CString.Set.empty

(* Errors occurring while lexing (explained as "Lexer error: ...") *)

module Error = struct

  type t =
    | Illegal_character
    | Unterminated_comment
    | Unterminated_string
    | Undefined_token
    | Bad_token of string
    | UnsupportedUnicode of int

  exception E of t

  let to_string x =
    "Syntax Error: Lexer: " ^
      (match x with
         | Illegal_character -> "Illegal character"
         | Unterminated_comment -> "Unterminated comment"
         | Unterminated_string -> "Unterminated string"
         | Undefined_token -> "Undefined token"
         | Bad_token tok -> Format.sprintf "Bad token %S" tok
         | UnsupportedUnicode x ->
             Printf.sprintf "Unsupported Unicode character (0x%x)" x)

  (* Require to fix the Camlp4 signature *)
  let print ppf x = Pp.pp_with ~pp_tag:Ppstyle.pp_tag ppf (Pp.str (to_string x))

end
open Error

let err loc str = Loc.raise (Compat.to_coqloc loc) (Error.E str)

let bad_token str = raise (Error.E (Bad_token str))

(* Lexer conventions on tokens *)

type token_kind =
  | Utf8Token of (Unicode.status * int)
  | AsciiChar
  | EmptyStream

let error_utf8 loc cs =
  let bp = Stream.count cs in
  Stream.junk cs; (* consume the char to avoid read it and fail again *)
  let loc = set_loc_pos loc bp (bp+1) in
  err loc Illegal_character

let utf8_char_size loc cs = function
  (* Utf8 leading byte *)
  | '\x00'..'\x7F' -> 1
  | '\xC0'..'\xDF' -> 2
  | '\xE0'..'\xEF' -> 3
  | '\xF0'..'\xF7' -> 4
  | _ (* '\x80'..\xBF'|'\xF8'..'\xFF' *) -> error_utf8 loc cs

let njunk n = Util.repeat n Stream.junk

let check_utf8_trailing_byte loc cs c =
  if not (Int.equal (Char.code c land 0xC0) 0x80) then error_utf8 loc cs

(* Recognize utf8 blocks (of length less than 4 bytes) *)
(* but don't certify full utf8 compliance (e.g. no emptyness check) *)
let lookup_utf8_tail loc c cs =
  let c1 = Char.code c in
  if Int.equal (c1 land 0x40) 0 || Int.equal (c1 land 0x38) 0x38 then error_utf8 loc cs
  else
    let n, unicode =
      if Int.equal (c1 land 0x20) 0 then
      match Stream.npeek 2 cs with
      | [_;c2] ->
          check_utf8_trailing_byte loc cs c2;
          2, (c1 land 0x1F) lsl 6 + (Char.code c2 land 0x3F)
      | _ -> error_utf8 loc cs
      else if Int.equal (c1 land 0x10) 0 then
      match Stream.npeek 3 cs with
      | [_;c2;c3] ->
          check_utf8_trailing_byte loc cs c2;
	  check_utf8_trailing_byte loc cs c3;
          3, (c1 land 0x0F) lsl 12 + (Char.code c2 land 0x3F) lsl 6 +
          (Char.code c3 land 0x3F)
      | _ -> error_utf8 loc cs
      else match Stream.npeek 4 cs with
      | [_;c2;c3;c4] ->
          check_utf8_trailing_byte loc cs c2;
	  check_utf8_trailing_byte loc cs c3;
          check_utf8_trailing_byte loc cs c4;
          4, (c1 land 0x07) lsl 18 + (Char.code c2 land 0x3F) lsl 12 +
          (Char.code c3 land 0x3F) lsl 6 + (Char.code c4 land 0x3F)
      | _ -> error_utf8 loc cs
    in
    Utf8Token (Unicode.classify unicode, n)

let lookup_utf8 loc cs =
  match Stream.peek cs with
    | Some ('\x00'..'\x7F') -> AsciiChar
    | Some ('\x80'..'\xFF' as c) -> lookup_utf8_tail loc c cs
    | None -> EmptyStream

let unlocated f x = f x
  (** FIXME: should we still unloc the exception? *)
(*   try f x with Loc.Exc_located (_, exc) -> raise exc *)

let check_keyword str =
  let rec loop_symb = parser
    | [< ' (' ' | '\n' | '\r' | '\t' | '"') >] -> bad_token str
    | [< s >] ->
        match unlocated lookup_utf8 Compat.CompatLoc.ghost s with
        | Utf8Token (_,n) -> njunk n s; loop_symb s
        | AsciiChar -> Stream.junk s; loop_symb s
        | EmptyStream -> ()
  in
  loop_symb (Stream.of_string str)

let check_ident str =
  let rec loop_id intail = parser
    | [< ' ('a'..'z' | 'A'..'Z' | '_'); s >] ->
        loop_id true s
    | [< ' ('0'..'9' | ''') when intail; s >] ->
        loop_id true s
    | [< s >] ->
        match unlocated lookup_utf8 Compat.CompatLoc.ghost s with
        | Utf8Token (Unicode.Letter, n) -> njunk n s; loop_id true s
        | Utf8Token (Unicode.IdentPart, n) when intail ->
          njunk n s;
          loop_id true s
        | EmptyStream -> ()
        | Utf8Token _ | AsciiChar -> bad_token str
  in
  loop_id false (Stream.of_string str)

let is_ident str =
  try let _ = check_ident str in true with Error.E _ -> false

(* Keyword and symbol dictionary *)
let token_tree = ref empty_ttree

let is_keyword s =
  try match (ttree_find !token_tree s).node with None -> false | Some _ -> true
  with Not_found -> false

let add_keyword str =
  if not (is_keyword str) then
    begin
      check_keyword str;
      token_tree := ttree_add !token_tree str
    end

let remove_keyword str =
  token_tree := ttree_remove !token_tree str

let keywords () = ttree_elements !token_tree

(* Freeze and unfreeze the state of the lexer *)
type frozen_t = ttree

let freeze () = !token_tree
let unfreeze tt = (token_tree := tt)

(* The string buffering machinery *)

let buff = ref (String.create 80)

let store len x =
  if len >= String.length !buff then
    buff := !buff ^ String.create (String.length !buff);
  !buff.[len] <- x;
  succ len

let rec nstore n len cs =
  if n>0 then nstore (n-1) (store len (Stream.next cs)) cs else len

let get_buff len = String.sub !buff 0 len

(* The classical lexer: idents, numbers, quoted strings, comments *)

let warn_unrecognized_unicode =
  CWarnings.create ~name:"unrecognized-unicode" ~category:"parsing"
         (fun (u,id) ->
          strbrk (Printf.sprintf "Not considering unicode character \"%s\" of unknown \
                                  lexical status as part of identifier \"%s\"." u id))

let rec ident_tail loc len = parser
  | [< ' ('a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_' as c); s >] ->
      ident_tail loc (store len c) s
  | [< s >] ->
      match lookup_utf8 loc s with
      | Utf8Token ((Unicode.IdentPart | Unicode.Letter), n) ->
          ident_tail loc (nstore n len s) s
      | Utf8Token (Unicode.Unknown, n) ->
          let id = get_buff len in
          let u = String.concat "" (List.map (String.make 1) (Stream.npeek n s)) in
          warn_unrecognized_unicode ~loc:!@loc (u,id); len
      | _ -> len

let rec number len = parser
  | [< ' ('0'..'9' as c); s >] -> number (store len c) s
  | [< >] -> len

let warn_comment_terminator_in_string =
  CWarnings.create ~name:"comment-terminator-in-string" ~category:"parsing"
         (fun () ->
          (strbrk
             "Not interpreting \"*)\" as the end of current \
              non-terminated comment because it occurs in a \
              non-terminated string of the comment."))

(* If the string being lexed is in a comment, [comm_level] is Some i with i the
   current level of comments nesting. Otherwise, [comm_level] is None. *)
let rec string loc ~comm_level bp len = parser
  | [< ''"'; esc=(parser [<''"' >] -> true | [< >] -> false); s >] ->
      if esc then string loc ~comm_level bp (store len '"') s else (loc, len)
  | [< ''('; s >] ->
      (parser
        | [< ''*'; s >] ->
            string loc
              (Option.map succ comm_level)
              bp (store (store len '(') '*')
              s
        | [< >] ->
            string loc comm_level bp (store len '(') s) s
  | [< ''*'; s >] ->
      (parser
        | [< '')'; s >] ->
            let () = match comm_level with
            | Some 0 ->
	       warn_comment_terminator_in_string ~loc:!@loc ()
            | _ -> ()
            in
            let comm_level = Option.map pred comm_level in
            string loc comm_level bp (store (store len '*') ')') s
        | [< >] ->
            string loc comm_level bp (store len '*') s) s
  | [< ''\n' as c; s >] ep ->
     (* If we are parsing a comment, the string if not part of a token so we
     update the first line of the location. Otherwise, we update the last
     line. *)
     let loc =
       if Option.has_some comm_level then bump_loc_line loc ep
       else bump_loc_line_last loc ep
     in
     string loc comm_level bp (store len c) s
  | [< 'c; s >] -> string loc comm_level bp (store len c) s
  | [< _ = Stream.empty >] ep ->
     let loc = set_loc_pos loc bp ep in
     err loc Unterminated_string

(* Hook for exporting comment into xml theory files *)
let (f_xml_output_comment, xml_output_comment) = Hook.make ~default:ignore ()

(* To associate locations to a file name *)
let current_file = ref None

(* Utilities for comments in beautify *)
let comment_begin = ref None
let comm_loc bp = match !comment_begin with
| None -> comment_begin := Some bp
| _ -> ()

let comments = ref []
let current_comment = Buffer.create 8192
let between_commands = ref true

let rec split_comments comacc acc pos = function
    [] -> comments := List.rev acc; comacc
  | ((b,e),c as com)::coms ->
      (* Take all comments that terminates before pos, or begin exactly
         at pos (used to print comments attached after an expression) *)
      if e<=pos || pos=b then split_comments (c::comacc) acc pos coms
      else split_comments comacc (com::acc) pos coms

let extract_comments pos = split_comments [] [] pos !comments

(* The state of the lexer visible from outside *)
type lexer_state = int option * string * bool * ((int * int) * string) list * string option

let init_lexer_state f = (None,"",true,[],f)
let set_lexer_state (o,s,b,c,f) =
  comment_begin := o;
  Buffer.clear current_comment; Buffer.add_string current_comment s;
  between_commands := b;
  comments := c;
  current_file := f
let release_lexer_state () =
  (!comment_begin, Buffer.contents current_comment, !between_commands, !comments, !current_file)
let drop_lexer_state () =
    set_lexer_state (init_lexer_state None)

let real_push_char c = Buffer.add_char current_comment c

(* Add a char if it is between two commands, if it is a newline or
   if the last char is not a space itself. *)
let push_char c =
  if
    !between_commands || List.mem c ['\n';'\r'] ||
    (List.mem c [' ';'\t']&&
     (Int.equal (Buffer.length current_comment) 0 ||
      not (let s = Buffer.contents current_comment in
           List.mem s.[String.length s - 1] [' ';'\t';'\n';'\r'])))
  then
    real_push_char c

let push_string s = Buffer.add_string current_comment s

let null_comment s =
  let rec null i =
    i<0 || (List.mem s.[i] [' ';'\t';'\n';'\r'] && null (i-1)) in
  null (String.length s - 1)

let comment_stop ep =
  let current_s = Buffer.contents current_comment in
  if !Flags.xml_export && Buffer.length current_comment > 0 &&
    (!between_commands || not(null_comment current_s)) then
      Hook.get f_xml_output_comment current_s;
  (if !Flags.beautify && Buffer.length current_comment > 0 &&
    (!between_commands || not(null_comment current_s)) then
    let bp = match !comment_begin with
        Some bp -> bp
      | None ->
          Feedback.msg_notice
            (str "No begin location for comment '"
             ++ str current_s ++str"' ending at  "
             ++ int ep);
          ep-1 in
    comments := ((bp,ep),current_s) :: !comments);
  Buffer.clear current_comment;
  comment_begin := None;
  between_commands := false

let rec comment loc bp = parser bp2
  | [< ''(';
       loc = (parser
              | [< ''*'; s >] -> push_string "(*"; comment loc bp s
              | [< >] -> push_string "("; loc );
       s >] -> comment loc bp s
  | [< ''*';
       loc = parser
         | [< '')' >] -> push_string "*)"; loc
         | [< s >] -> real_push_char '*'; comment loc bp s >] -> loc
  | [< ''"'; s >] ->
      let loc, len = string loc ~comm_level:(Some 0) bp2 0 s in
      push_string "\""; push_string (get_buff len); push_string "\"";
      comment loc bp s
  | [< _ = Stream.empty >] ep ->
      let loc = set_loc_pos loc bp ep in
      err loc Unterminated_comment
  | [< ''\n' as z; s >] ep -> real_push_char z; comment (bump_loc_line loc ep) bp s
  | [< 'z; s >] -> real_push_char z; comment loc bp s

(* Parse a special token, using the [token_tree] *)

(* Peek as much utf-8 lexemes as possible *)
(* and retain the longest valid special token obtained *)
let rec progress_further loc last nj tt cs =
  try progress_from_byte loc last nj tt cs (List.nth (Stream.npeek (nj+1) cs) nj)
  with Failure _ -> last

and update_longest_valid_token loc last nj tt cs =
  match tt.node with
  | Some _ as last' ->
    stream_njunk nj cs;
    progress_further loc last' 0 tt cs
  | None ->
    progress_further loc last nj tt cs

(* nj is the number of char peeked since last valid token *)
(* n the number of char in utf8 block *)
and progress_utf8 loc last nj n c tt cs =
  try
    let tt = CharMap.find c tt.branch in
    if Int.equal n 1 then
      update_longest_valid_token loc last (nj+n) tt cs
    else
      match Util.List.skipn (nj+1) (Stream.npeek (nj+n) cs) with
      | l when Int.equal (List.length l) (n - 1) ->
         List.iter (check_utf8_trailing_byte loc cs) l;
         let tt = List.fold_left (fun tt c -> CharMap.find c tt.branch) tt l in
         update_longest_valid_token loc last (nj+n) tt cs
      | _ ->
          error_utf8 loc cs
  with Not_found ->
    last

and progress_from_byte loc last nj tt cs c =
  progress_utf8 loc last nj (utf8_char_size loc cs c) c tt cs

let find_keyword loc id s =
  let tt = ttree_find !token_tree id in
  match progress_further loc tt.node 0 tt s with
  | None -> raise Not_found
  | Some c -> KEYWORD c

let process_sequence loc bp c cs =
  let rec aux n cs =
    match Stream.peek cs with
    | Some c' when c == c' -> Stream.junk cs; aux (n+1) cs
    | _ -> BULLET (String.make n c), set_loc_pos loc bp (Stream.count cs)
  in
  aux 1 cs

(* Must be a special token *)
let process_chars loc bp c cs =
  let t = progress_from_byte loc None (-1) !token_tree cs c in
  let ep = Stream.count cs in
  match t with
    | Some t -> (KEYWORD t, set_loc_pos loc bp ep)
    | None ->
        let ep' = bp + utf8_char_size loc cs c in
        njunk (ep' - ep) cs;
	let loc = set_loc_pos loc bp ep' in
        err loc Undefined_token

(* Parse what follows a dot *)

let parse_after_dot loc c bp =
  parser
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as d); len = ident_tail loc (store 0 d); s >] ->
      let field = get_buff len in
      (try find_keyword loc ("."^field) s with Not_found -> FIELD field)
  | [< s >] ->
      match lookup_utf8 loc s with
      | Utf8Token (Unicode.Letter, n) ->
          let len = ident_tail loc (nstore n 0 s) s in
          let field = get_buff len in
          (try find_keyword loc ("."^field) s with Not_found -> FIELD field)
      | AsciiChar | Utf8Token _ | EmptyStream -> fst (process_chars loc bp c s)

(* Parse what follows a question mark *)

let parse_after_qmark loc bp s =
  match Stream.peek s with
    | Some ('a'..'z' | 'A'..'Z' | '_') -> LEFTQMARK
    | None -> KEYWORD "?"
    | _ ->
        match lookup_utf8 loc s with
          | Utf8Token (Unicode.Letter, _) -> LEFTQMARK
          | AsciiChar | Utf8Token _ | EmptyStream ->
            fst (process_chars loc bp '?' s)

let blank_or_eof cs =
  match Stream.peek cs with
    | None -> true
    | Some (' ' | '\t' | '\n' |'\r') -> true
    | _ -> false

(* Parse a token in a char stream *)

let rec next_token loc = parser bp
  | [< ''\n' as c; s >] ep ->
      comm_loc bp; push_char c; next_token (bump_loc_line loc ep) s
  | [< '' ' | '\t' | '\r' as c; s >] ->
      comm_loc bp; push_char c; next_token loc s
  | [< ''.' as c; t = parse_after_dot loc c bp; s >] ep ->
      comment_stop bp;
      (* We enforce that "." should either be part of a larger keyword,
         for instance ".(", or followed by a blank or eof. *)
      let () = match t with
      | KEYWORD ("." | "...") ->
        if not (blank_or_eof s) then
	  err (set_loc_pos loc bp (ep+1)) Undefined_token;
	between_commands := true;
      | _ -> ()
      in
      (t, set_loc_pos loc bp ep)
  | [< ' ('-'|'+'|'*' as c); s >] ->
      let t,new_between_commands =
        if !between_commands then process_sequence loc bp c s, true
        else process_chars loc bp c s,false
      in
      comment_stop bp; between_commands := new_between_commands; t
  | [< ''?'; s >] ep ->
      let t = parse_after_qmark loc bp s in
      comment_stop bp; (t, set_loc_pos loc bp ep)
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c);
       len = ident_tail loc (store 0 c); s >] ep ->
      let id = get_buff len in
      comment_stop bp;
      (try find_keyword loc id s with Not_found -> IDENT id), set_loc_pos loc bp ep
  | [< ' ('0'..'9' as c); len = number (store 0 c) >] ep ->
      comment_stop bp;
      (INT (get_buff len), set_loc_pos loc bp ep)
  | [< ''\"'; (loc,len) = string loc None bp 0 >] ep ->
      comment_stop bp;
      (STRING (get_buff len), set_loc_pos loc bp ep)
  | [< ' ('(' as c);
      t = parser
        | [< ''*'; s >] ->
            comm_loc bp;
            push_string "(*";
            let loc = comment loc bp s in next_token loc s
        | [< t = process_chars loc bp c >] -> comment_stop bp; t >] ->
      t
  | [< ' ('{' | '}' as c); s >] ep ->
      let t,new_between_commands =
        if !between_commands then (KEYWORD (String.make 1 c), set_loc_pos loc bp ep), true
        else process_chars loc bp c s, false
      in
      comment_stop bp; between_commands := new_between_commands; t
  | [< s >] ->
      match lookup_utf8 loc s with
        | Utf8Token (Unicode.Letter, n) ->
            let len = ident_tail loc (nstore n 0 s) s in
            let id = get_buff len in
            let ep = Stream.count s in
            comment_stop bp;
            (try find_keyword loc id s with Not_found -> IDENT id), set_loc_pos loc bp ep
        | AsciiChar | Utf8Token ((Unicode.Symbol | Unicode.IdentPart | Unicode.Unknown), _) ->
            let t = process_chars loc bp (Stream.next s) s in
            comment_stop bp; t
        | EmptyStream ->
            comment_stop bp; (EOI, set_loc_pos loc bp (bp+1))

(* (* Debug: uncomment this for tracing tokens seen by coq...*)
let next_token loc s =
  let (t,loc as r) = next_token loc s in
  Printf.eprintf "(line %i, %i-%i)[%s]\n%!" (Ploc.line_nb loc) (Ploc.first_pos loc) (Ploc.last_pos loc) (Tok.to_string t);
  r *)

(* Location table system for creating tables associating a token count
   to its location in a char stream (the source) *)

let locerr () = invalid_arg "Lexer: location function"

let loct_create () = Hashtbl.create 207

let loct_func loct i =
  try Hashtbl.find loct i with Not_found -> locerr ()

let loct_add loct i loc = Hashtbl.add loct i loc

(** {6 The lexer of Coq} *)

(** Note: removing a token.
   We do nothing because [remove_token] is called only when removing a grammar
   rule with [Grammar.delete_rule]. The latter command is called only when
   unfreezing the state of the grammar entries (see GRAMMAR summary, file
   env/metasyntax.ml). Therefore, instead of removing tokens one by one,
   we unfreeze the state of the lexer. This restores the behaviour of the
   lexer. B.B. *)

IFDEF CAMLP5 THEN

type te = Tok.t

(** Names of tokens, for this lexer, used in Grammar error messages *)

let token_text = function
  | ("", t) -> "'" ^ t ^ "'"
  | ("IDENT", "") -> "identifier"
  | ("IDENT", t) -> "'" ^ t ^ "'"
  | ("INT", "") -> "integer"
  | ("INT", s) -> "'" ^ s ^ "'"
  | ("STRING", "") -> "string"
  | ("EOI", "") -> "end of input"
  | (con, "") -> con
  | (con, prm) -> con ^ " \"" ^ prm ^ "\""

let func cs =
  let loct = loct_create () in
  let cur_loc = ref (Compat.make_loc !current_file 1 0 0 0) in
  let ts =
    Stream.from
      (fun i ->
         let (tok, loc) = next_token !cur_loc cs in
	 cur_loc := Compat.after loc;
         loct_add loct i loc; Some tok)
  in
  (ts, loct_func loct)

let lexer = {
  Token.tok_func = func;
  Token.tok_using =
    (fun pat -> match Tok.of_pattern pat with
       | KEYWORD s -> add_keyword s
       | _ -> ());
  Token.tok_removing = (fun _ -> ());
  Token.tok_match = Tok.match_pattern;
  Token.tok_comm = None;
  Token.tok_text = token_text }

ELSE (* official camlp4 for ocaml >= 3.10 *)

module M_ = Camlp4.ErrorHandler.Register (Error)

module Loc = Compat.CompatLoc
module Token = struct
  include Tok (* Cf. tok.ml *)
  module Loc = Compat.CompatLoc
  module Error = Camlp4.Struct.EmptyError
  module Filter = struct
    type token_filter = (Tok.t * Loc.t) Stream.t -> (Tok.t * Loc.t) Stream.t
    type t = unit
    let mk _is_kwd = ()
    let keyword_added () kwd _ = add_keyword kwd
    let keyword_removed () _ = ()
    let filter () x = x
    let define_filter () _ = ()
  end
end

let mk () =
  let loct = loct_create () in
  let cur_loc = ref (Compat.make_loc !current_file 1 0 0 0) in
  let rec self init_loc (* FIXME *) =
    parser i
       [< (tok, loc) = next_token !cur_loc; s >] ->
            cur_loc := Compat.set_loc_file loc !current_file;
	    loct_add loct i loc;
            [< '(tok, loc); self init_loc s >]
      | [< >] -> [< >]
  in
  self

END

(** Terminal symbols interpretation *)

let is_ident_not_keyword s =
  is_ident s && not (is_keyword s)

let is_number s =
  let rec aux i =
    Int.equal (String.length s) i ||
    match s.[i] with '0'..'9' -> aux (i+1) | _ -> false
  in aux 0

let strip s =
  let len =
    let rec loop i len =
      if Int.equal i (String.length s) then len
      else if s.[i] == ' ' then loop (i + 1) len
      else loop (i + 1) (len + 1)
    in
    loop 0 0
  in
  if len == String.length s then s
  else
    let s' = String.create len in
    let rec loop i i' =
      if i == String.length s then s'
      else if s.[i] == ' ' then loop (i + 1) i'
      else begin s'.[i'] <- s.[i]; loop (i + 1) (i' + 1) end
    in
    loop 0 0

let terminal s =
  let s = strip s in
  let () = match s with "" -> failwith "empty token." | _ -> () in
  if is_ident_not_keyword s then IDENT s
  else if is_number s then INT s
  else KEYWORD s
