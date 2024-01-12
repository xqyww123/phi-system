#include <stdbool.h>

typedef int K;
typedef int V;

struct KV_pair {
  K k;
  V v;
};

struct BinTree {
  struct BinTree *left;
  struct KV_pair data;
  struct BinTree *right;
};

struct AVL_data {
  int height;
  V v;
};

struct AVL_KV {
  K k;
  struct AVL_data v;
};

struct AVLTree {
  struct BinTree *left;
  struct AVL_KV data;
  struct BinTree *right;
};


V lookup_bst (struct BinTree *addr, K k) {
  K k2 = addr->data.k;
  if (k2 == k) return addr->data.v;
  else if (k < k2)
    return lookup_bst (addr->left, k);
  else
    return lookup_bst (addr->right, k);
}

bool defined_bst (struct BinTree *addr, K k) {
  if (addr == 0) return false;
  K k2 = addr->data.k;
  if (k2 == k) return true;
  else if (k < k2)
    return defined_bst (addr->left, k);
  else
    return defined_bst (addr->right, k);
}

void insert_bst (struct BinTree *addr, K k, V v) {
  if (addr == 0) {
    struct BinTree *ret = calloc(sizeof(struct BinTree), 1);
    ret -> data -> k = k;
    ret -> data -> v = v;
    return ret;
  } else {
    K k2 = addr -> data -> k;
    if (k == k2) {
      struct BinTree *aL = insert_bst (addr -> left, k, v);
      addr -> left = aL;
      return addr;
    } else {
      struct BinTree *aL = insert_bst (addr -> right, k, v);
      addr -> right = aL;
      return addr;
    }
  }
}

int Max(int x, int y) {
  if (x < y) return y; else return x;
}

int height_of (struct BinTree *addr) {
  if (addr == 0)
    return 0;
  else
    return addr -> data -> v -> height;
}

void maintain_i (struct BinTree *aD) {
  struct BinTree *B = aD -> left;
  struct BinTree *E = aD -> right;
  int HB = height_of(B);
  int HE = height_of(E);
  if (HB == HE + 2) {
    struct BinTree *A = B -> left;
    struct BinTree *C = B -> right;
    int HA = height_of(A);
    int HC = height_of(C);
    if (HC <= HA) {
      aD -> left = C;
      int HD2 = Max(HC, HE) + 1;
      aD -> data -> v -> height = HD2;
      B -> right = aD;
      B -> data -> v -> height = Max(HA, HD2) + 1;
      return B;
    } else {
      struct BinTree *CL = C -> left;
      struct BinTree *CR = C -> right;
      B -> right = CL;
      int HB2 = Max(HA, height_of(CL)) + 1;
      B -> data -> v -> height = HB2;
      aD -> left = C -> right;
      int HD2 = Max(HE, height_of(CR)) + 1;
      aD -> data -> v -> height = HD2;
      C -> left = B;
      C -> right = aD;
      C -> data -> v -> height = Max(HB2, HD2) + 1;
      return C;
    }
  } else if (HE == HB + 2) {
    struct BinTree *F = E -> left;
    struct BinTree *G = E -> right;
    int HF = height_of (F);
    int HG = height_of (G);
    if (HF <= HG) {
      aD -> right = F;
      int HD2 = Max(HB, HF) + 1;
      aD -> data -> v -> height = HD2;
      E -> left = aD;
      E -> data -> v -> height = Max(HD2, HG) + 1;
      return E;
    } else {
      struct BinTree *FL = F -> left;
      struct BinTree *FR = F -> right;
      aD -> right = FL;
      int HD2 = Max(HB, height_of(FL)) + 1;
      aD -> data -> v -> height = HD2;
      E -> left = FR;
      int HE2 = Max(height_of(FR), HG) + 1;
      E -> data -> v -> height = HE2;
      F -> left = aD;
      F -> right = E;
      F -> data -> height = Max(HD2, HE2) + 1;
      return F;
    }
  } else {
    aD -> data -> v -> height = Max(height_of(aD -> left), height_of(aD -> right)) + 1;
    return aD;
  }
}

void insert_avl (struct BinTree *addr, K k, V v) {
  if (addr == 0) {
    struct BinTree *ret = calloc(sizeof(struct BinTree), 1);
    ret -> data -> k = k;
    ret -> data -> v -> v = v;
    ret -> data -> v -> height = 1;
    return ret;
  } else {
    K k2 = addr -> data -> k;
    if (k2 == k) {
      addr -> data -> v -> v = v;
      return addr;
    } else {
      if (k < k2) {
        struct BinTree *aL = insert_avl_i (addr -> left, k, v);
        addr -> left = aL;
        return maintain_i(addr);
      } else {
        struct BinTree *aR = insert_avl_i (addr -> right, k, v);
        addr -> right = aR;
        return maintain_i(addr);
      }
    }
  }
}


