void qsort (int* l, int len) {
  if (len < 1)
    return;
  else {
    int pivot = l[len - 1];
    int d = 0;
    for (int n = 0; n < len; ++n) {
      int x = l[n];
      if (x <= pivot) {
        l[n] = l[d];
        l[d] = x;
        ++d;
      }
    }
    qsort (l, d-1) ;
    qsort (l+d, len-d) ;
  }
}


