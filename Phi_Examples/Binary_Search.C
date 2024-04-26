
int binary_search_array (int* ptr, int lower, int upper, int k)
{
  if (ptr[lower] <= k) {
    return lower;
  } else {
    int l = lower, u = upper;
    while (l + 1 < u) {
      int m = l + (u - l) / 2;
      if (ptr[m] <= k)
        u = m;
      else
        l = m;
    }
    return u;
  }
}

typedef bool (*test_function) (int i);

int generalize_binary_search (int lower, int upper, test_function F)
{
  if (F (lower)) {
    return lower;
  } else {
    int l = lower, u = upper;
    while (l + 1 < u) {
      int m = l + (u - l) / 2 ;
      if (F(m))
        u = m;
      else
        l = m;
    }
    return u;
  }
}
