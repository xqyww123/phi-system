signature PHI_ENVIR = sig

datatype runtime_mode = PRODUCTION | EDITING | CLEAN_BUILDING
val runtime_mode : unit -> runtime_mode

end

structure Phi_Envir : PHI_ENVIR = struct

datatype runtime_mode = PRODUCTION | EDITING | CLEAN_BUILDING
fun runtime_mode () =
  case getenv "PHISYS_MODE"
    of "production" => PRODUCTION
     | "normal" => EDITING
     | "building" => CLEAN_BUILDING
     | "" => EDITING
     | mode => error ("Bad environment variable PHISYS_MODE = " ^ mode)

end
