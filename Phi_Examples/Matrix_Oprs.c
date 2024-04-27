#include <stdlib.h>
#define nn 10
#define MM 1024
#define NN 1024

typedef int Mat[MM][NN];

void zero_mat (Mat* a, int i, int j, int m, int n) {
  for (int k=0; k<m; ++k) {
    for (int h=0; h<n; ++h) {
      *a[i+k][j+h] = 0;
    }
  }
}

Mat* new_mat () {
  return calloc (sizeof(Mat), 1);
}

void del_mat (Mat* a) {
  free(a);
}

void copy_mat (Mat* x, int ix, int jx, Mat* y, int iy, int jy, int m, int n) {
  for (int k=0; k<m; ++k) {
    for (int h=0; h<n; ++h) {
      *x[ix+k][jx+h] = *y[ix+k][jx+h];
    }
  }
}

void add_mat (Mat* x, int ix, int jx, Mat* y, int iy, int jy, int m, int n) {
  for (int k=0; k<m; ++k) {
    for (int h=0; h<n; ++h) {
      *x[ix+k][jx+h] = *x[ix+k][jx+h] + *y[ix+k][jx+h];
    }
  }
}

void sub_mat (Mat* x, int ix, int jx, Mat* y, int iy, int jy, int m, int n) {
  for (int k=0; k<m; ++k) {
    for (int h=0; h<n; ++h) {
      *x[ix+k][jx+h] = *x[ix+k][jx+h] - *y[ix+k][jx+h];
    }
  }
}

void strassen (Mat* A, int ia, int ja, Mat* B, int ib, int jb,
               Mat* C, int ic, int jc, Mat* D, int id, int jd,
               int n) {
  if (n = 0)
    *A[ia][ja] = *A[ia][ja] * *B[ib][jb];
  else {
    int N = 1 << (n-1);
    int iam = ia + N;
    int jam = ja + N;
    int ibm = ib + N;
    int jbm = jb + N;
    int icm = ic + N;
    int jcm = jc + N;
    int idm = id + N;
    int jdm = jd + N;

    copy_mat (C, ic , jc , A, ia , ja , N, N);
    add_mat  (C, ic , jc , A, iam, jam, N, N);
    copy_mat (D, id , jd , A, ib , jb , N, N);
    add_mat  (D, id , jd , A, ibm, jbm, N, N);
    strassen (C, ic , jc , D, idm, jdm, C, ic , jcm, C, icm, jc , n-1);

    copy_mat (C, ic , jcm, A, iam, ja , N, N);
    add_mat  (C, ic , jcm, A, iam, jam, N, N);
    strassen (C, ic , jcm, B, ib , jb , C, icm, jc , C, icm, jcm, n-1);

    copy_mat (D, idm, jdm, B, ib , jbm, N, N);
    sub_mat  (D, idm, jdm, B, ibm, jbm, N, N);
    copy_mat (C, icm, jc , A, ia , ja , N, N);
    strassen (C, icm, jc , D, idm, jd , C, icm, jcm, D, id , jd , n-1);

    copy_mat (D, idm, jdm, B, ibm, jb , N, N);
    sub_mat  (D, idm, jdm, B, ib , jb , N, N);
    copy_mat (C, icm, jcm, A, iam, jam, N, N);
    strassen (C, icm, jcm, D, idm, jdm, D, id , jd , D, id , jdm, n-1);

    copy_mat (D, id , jd , A, ia , ja , N, N);
    add_mat  (D, id , jd , A, ia , jam, N, N);
    strassen (D, id , jd , B, ibm, jbm, D, id , jdm, D, idm, jd , n-1);

    copy_mat (D, id , jdm, A, iam, ja , N, N);
    sub_mat  (D, id , jdm, A, ia , ja , N, N);
    copy_mat (D, idm, jdm, B, ib , jb , N, N);
    add_mat  (D, idm, jdm, B, ib , jbm, N, N);
    strassen (D, id , jdm, D, idm, jdm, D, idm, jd , A, ia , ja , n-1);

    copy_mat (D, idm, jd , A, ia , jam, N, N);
    sub_mat  (D, idm, jd , A, iam, jam, N, N);
    copy_mat (D, idm, jdm, B, ibm, jb , N, N);
    add_mat  (D, idm, jdm, B, ibm, jbm, N, N);
    strassen (D, idm, jd , D, idm, jdm, A, ia , ja , A, ia , jam, n-1);

    add_mat  (D, idm, jd , C, ic , jc , N, N);
    add_mat  (D, idm, jd , C, icm, jcm, N, N);
    sub_mat  (D, idm, jd , D, id , jd , N, N);
    copy_mat (A, ia , ja , D, idm, jd , N, N);

    add_mat  (D, id , jd , A, icm, jcm, N, N);
    copy_mat (A, ia , jam, D, id , jd , N, N);

    add_mat  (C, icm, jcm, C, ic , jcm, N, N);
    copy_mat (A, iam, ja , C, icm, jcm, N, N);

    add_mat  (D, id , jdm, C, ic , jc , N, N);
    sub_mat  (D, id , jdm, C, ic , jcm, N, N);
    add_mat  (D, id , jdm, C, icm, jc , N, N);
    copy_mat (A, iam, jam, D, id , jdm, N, N);
  }
}

void strassen_mul (Mat* A, Mat* B) {
  Mat* C = new_mat ();
  Mat* D = new_mat ();
  strassen (A, 0, 0, B, 0, 0, C, 0, 0, D, 0, 0, nn);
  del_mat (C);
  del_mat (D);
}

