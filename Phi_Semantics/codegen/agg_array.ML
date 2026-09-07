structure C'G_PhiSem_Aggregate_Array = struct local open Phi_C'G in
fun sem_array_T_ n T = T #-> (fn t => defty_array t (string_of_int n))
end end
