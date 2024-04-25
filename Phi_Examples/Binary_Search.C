typedef bool (*test_function) (int i);

int binary_search (int lower, int upper, test_function F) {
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
