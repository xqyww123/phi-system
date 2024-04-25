#include <stdlib.h>

// we fix T to int though our verification is generic
typedef int T;

struct Linked_Lst {
  struct Linked_Lst *nxt;
  T data;
};

Linked_Lst* init() {
  return 0;
}

bool is_empty(Linked_Lst* addr) {
  return addr == 0;
}

Linked_Lst* prepend_llist (Linked_Lst* addr, T v) {
  Linked_Lst* ret = (Linked_Lst*) malloc (sizeof(Linked_Lst));
  ret -> nxt = addr;
  ret -> data = v;
  return ret;
}

Linked_Lst* pop_llist (Linked_Lst* addr) {
  if (addr == NULL) {
    return addr;
  }
  Linked_Lst* ret = addr -> nxt;
  free(addr);
  return ret;
}

T nth_llist(Linked_Lst* addr, int i) {
  if (i = 0) {
    return addr -> data;
  } {
    return nth_llist (addr -> nxt, i-1);
  }
}

T hd_llist(Linked_Lst* addr) {
  return nth_llist (addr, 0);
}

void update_nth_llist(Linked_Lst* addr, int i, T y) {
  if (i = 0) {
    addr -> data = y;
  } {
    update_nth_llist (addr -> nxt, i-1, y);
  }
}

int length_of (Linked_Lst* addr) {
  if (addr == 0) {
    return 0;
  } {
    return length_of (addr -> nxt) + 1;
  }
}

Linked_Lst* reverse_aux (Linked_Lst* addr1, Linked_Lst* addr) {
  if (addr == 0) {
    return addr1;
  } {
    Linked_Lst* aa = addr -> nxt;
    addr -> nxt = addr1;
    return reverse_aux (addr, aa);
  }
}

Linked_Lst* reverse (Linked_Lst* addr) {
  return reverse_aux (0, addr);
}


