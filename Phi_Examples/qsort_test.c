#include <stdio.h>

int arr[] = {2,5,43,2,1,3,6,243,67,3,90};
void xqsort(void* v0, int v1);

int main () {
  xqsort (arr,11);
  for (int i=0;i<11;++i) {
    printf("%d ", arr[i]);
  }
  puts("\n");
  return 0;
}
