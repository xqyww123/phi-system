structure Phi_CG : PHI_CG = struct

datatype V = V of string | V2 of V * V | V0 ;
fun dV (V s) = s | dV V0 = "" | dV _ = error "dV" ; fun lV[] = V0 | lV[v] = v | lV(a::b) = V2(a,lV b)


(*the instance name the next routine hook should take, if any*)
datatype frame = Named of string | Anonymous

type ctxt = string list list * string option * exn Symtab.table * string list list * int * frame
            (*current buffer*)
            (*the export name, seen only by the first routine hook of an export*)
            (*functions, typedefs and content keys, under distinct key prefixes*)
            (*outputs*)
            (*variable counter*)
            (*frame*)
type M = ctxt -> V * ctxt; type ty = M

val cat = String.concat; val catw = String.concatWith

val serial_c = Synchronized.var "Phi_CG" 1
fun serial pr = Synchronized.change_result serial_c (fn i => (pr ^ string_of_int i,i+1))
fun puts s (out::outs,pf,ftab,ss,vc,fr) = ((rev s@out)::outs,pf,ftab,ss,vc,fr); fun put s = puts [s];
fun puts' s = puts s #> put " " ; fun put' s = put s #> put " "
fun puts'' s = puts s #> put ";\n" #> pair V0; fun put'' s = put s #> put ";\n" #> pair V0

fun assign_var (out,pf,ftab,ss,vc,fr) = ("v" ^ string_of_int vc, (out,pf,ftab,ss,vc+1,fr))
fun get_frame (_,_,_,_,_,fr) = fr
fun set_frame fr (out,pf,ftab,ss,vc,_) = (out,pf,ftab,ss,vc,fr)

exception FUN of V -> M
exception KEY of string
fun fun_entry name = "F" ^ name
fun key_entry text = "K" ^ text
fun the_fun ftab name = case Symtab.lookup ftab (fun_entry name) of SOME (FUN G) => G
      | _ => raise Fail ("no function " ^ name)

(*the text of a function with its own name blanked; the name is a piece of its own followed by
  a piece beginning with "(", in the header and in every self-call (routine.ML), and no hook
  may put a piece taken from the program before a piece beginning with "("*)
fun content_key name text =
  let fun blank (s :: (rest as t :: _)) = (if s = name andalso String.isPrefix "(" t then "<self>" else s) :: blank rest
        | blank l = l
   in cat (blank text) end

(*the injective spelling of a name segment or a parameter text as a C identifier fragment: an
  underscore doubles, any other character outside letters and digits becomes two letters a..p
  (its byte in hexadecimal) followed by an underscore*)
fun spell_char #"_" = "__"
  | spell_char c = if Char.isAlphaNum c then str c
      else let val n = Char.ord c
            in String.implode [Char.chr (Char.ord #"a" + n div 16), Char.chr (Char.ord #"a" + n mod 16), #"_"] end
val spell = String.translate spell_char

(*the text a parameter contributes to an instance name; NONE when its value has no text*)
type keyp = ctxt -> string option * ctxt
val key_int  : int  -> keyp = pair o SOME o string_of_int
val key_bool : bool -> keyp = pair o SOME o Bool.toString
fun key_strs (P : ctxt -> string list * ctxt) : keyp = P #-> (pair o SOME o cat)

(*the instance name: f__, the segments of the constant's name, then the parameter texts, each
  with its length in front and a text after an A*)
fun mangle name (keys : keyp list) : ctxt -> string option * ctxt = fn c =>
  let val (texts, c') = fold_map I keys c
      fun seg s = string_of_int (size s) ^ s
   in if exists is_none texts then (NONE, c')
      else (SOME ("f__" ^ cat (map (seg o spell) (space_explode "." name))
                       ^ cat (map (fn t => let val s = spell (the t) in string_of_int (size s) ^ "A" ^ s end) texts)), c')
  end

(*an instance's body runs with its name in the frame; the frame is restored on exit*)
fun frame nameP (F : M) : M = fn c =>
  let val (name, c1) = nameP c
      val saved = get_frame c1
      val (v, c2) = F (set_frame (case name of SOME n => Named n | NONE => Anonymous) c1)
   in (v, set_frame saved c2) end
fun frame' nameP (F : V -> M) = fn v => frame nameP (F v)

(*Names and defines the function a routine hook prints, then prints the call.  The name is the
  export name if this is the first hook of an export, else the instance name in the frame, else
  a serial.  A function already defined under the name is only called.  Otherwise the body is
  printed and, unless at an export top, discarded when a function with the same content key
  exists.  At an export top a second copy is printed even if the body exists: an export must be
  a function under its own name; this happens when one instance is exported under two names or
  is defined internally before its export is reached.*)
fun new_fun F v (c as (outs,pf,ftab,ss,vc,fr)) =
  let val (name, alias) =
        case (pf, fr)
          of (SOME e, Named m) => (e, SOME m)
           | (SOME e, _)       => (e, NONE)
           | (NONE, Named n)   => (n, NONE)
           | (NONE, Anonymous) => (serial "f__", NONE)
   in case Symtab.lookup ftab (fun_entry name)
        of SOME (FUN G) => G v (outs, NONE, ftab, ss, vc, Anonymous)
         | _ =>
      let val (G, (out::outs', _, ftab', ss', _, _)) = F name ([]::outs, NONE, ftab, ss, 0, Anonymous)
          val text = rev out
          val key  = key_entry (content_key name text)
       in case (pf, Symtab.lookup ftab key)
            of (NONE, SOME (KEY m)) =>
                 let val G' = the_fun ftab m
                  in G' v (outs, NONE, Symtab.update (fun_entry name, FUN G') ftab, ss, vc, Anonymous) end
             | _ =>
                 let val ftab'' = ftab' |> Symtab.update (fun_entry name, FUN G)
                                       |> Symtab.default (key, KEY name)
                                       |> (case alias of SOME m => Symtab.update (fun_entry m, FUN G) | NONE => I)
                  in G v (outs', NONE, ftab'', text :: ss', vc, Anonymous) end
      end
  end

(*a letter followed by "__", or v followed by digits: the shapes of generated names*)
fun is_generated_name s =
  (size s >= 3 andalso String.substring (s, 1, 2) = "__")
  orelse (size s >= 2 andalso String.sub (s, 0) = #"v" andalso forall Char.isDigit (String.explode (String.extract (s, 1, NONE))))

fun interf name F ([],NONE,ftab,ss,0,Anonymous) =
  let val _ = is_generated_name name andalso
        error ("The export name " ^ quote name ^ " has the shape of a generated name (a letter followed by \"__\", or v followed by digits); choose another name")
      val (_,(_,_,ftab',ss',_,_)) = F V0 ([[]],SOME name,ftab,ss,0,Anonymous)
      val _ = Symtab.defined ftab' (fun_entry name) orelse
        error ("The export " ^ quote name ^ " produced no function: its body reaches no routine")
   in ([],NONE,ftab',ss',0,Anonymous) end

(*the file is opened only once every function has been printed, so a refused export leaves
  no file behind*)
fun codegen' prelude path G =
  let val (_,_,_,ss,_,_) = G([],NONE,Symtab.empty,[],0,Anonymous)
      val os = TextIO.openOut path; fun out s = TextIO.output (os, s)
   in out prelude; List.app (List.app out) (rev ss); TextIO.flushOut os; TextIO.closeOut os end

end
