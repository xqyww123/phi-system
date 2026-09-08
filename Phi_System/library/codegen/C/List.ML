structure C'G_List = struct structure list = struct val Nil_ = []; fun Cons_ a l = a :: l end
  val list_K = fn _ => pair NONE   (*a list parameter has no text yet*) end