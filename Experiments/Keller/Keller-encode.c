#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#define SBP

/* N is the dimension, S is the number of different shifts (modulo 1) */
/* In the paper, N = 7 and S = {3,4,6} */
int N, S;
int nvar = 0;
int *units, nunit;

/* converts indicator for index w, coordinate i, shift c
   to a CNF variable (x_{w,i,c} notation in paper) */
int convert(int w, int i, int c) {
    assert(w >= 0 && w < (1 << N));
    assert(i >= 0 && i < N);
    assert(c >= 0 && c < S);
    return S*N*w + S*i + c + 1;
}

/* Assert for every pair of cubes w, ww that they do not intersect
   and do not faceshare */
void gen_edges() {
  int var = (1 << N) * N * S;
  for (int w = 0; w < (1 << N); w++) {
    for (int ww = w+1; ww < (1 << N); ww++) {
      int j = 0;
      int xor = w ^ ww;

      /* of the bits which w and ww differ in, they must be EXACTLY the same in one place */
      for (int i = 0; i < N; i++)
        if (xor & (1 << i)) { j++; printf ("%i ", var + j); }
      printf ("0\n");

      j = 0;
      for (int i = 0; i < N; i++)
        if (xor & (1 << i)) {
          j++;
          for (int c = 0; c < S; c++) {
            printf ("-%i %i -%i 0\n", var + j, convert(w, i, c), convert (ww, i, c));
            printf ("-%i -%i %i 0\n", var + j, convert(w, i, c), convert (ww, i, c)); } }

       var += j;
       /* do w and ww differ only in one coordinate ? */
       if (__builtin_popcount(xor) == 1) {
         j = 0;
         for (int i = 0; i < N; i++)
           if (xor != (1 << i))
             for (int c = 0; c < S; c++) {
               j++;
               printf ("%i ", var + j); }
         printf ("0\n");

         j = 0;
         for (int i = 0; i < N; i++)
           if (xor != (1 << i)) {
             for (int c = 0; c < S; c++) {
               j++;
               printf ("-%i  %i  %i 0\n", var + j, convert(w, i, c), convert (ww, i, c));
               printf ("-%i -%i -%i 0\n", var + j, convert(w, i, c), convert (ww, i, c)); } }

         var += j;
       }
    }
  }
}

void sym_break() {
    // set c0
    for (int i = 0; i < N; i++) {
        printf ("%i 0\n", convert(0, i, 0));
    }
    // set c1
    printf ("%i 0\n", convert(1, 0, 0));
    printf ("%i 0\n", convert(1, 1, 1));
    for (int i = 2; i < N; i++) {
        printf ("%i 0\n", convert(1, i, 0));
    }

    // c3 sort zeros to the right
    for (int i = 2; i+1 < N; i++) {
        printf ("-%i %i 0\n", convert(3, i, 0), convert(3, i+1, 0));
    }

    // c3 has more nonzeros than c7
    for (int lastNz = 2; lastNz+1 < N; lastNz++) {
        for (int forcedZero = lastNz+1; forcedZero < N; forcedZero++) {
            // if c3[lastNz] != 0 and c3[lastNz+1] = 0,
            printf ("%i -%i ", convert(3,lastNz,0), convert(3,lastNz+1,0));
            // then c7 must have a zero in cols 2..lastNz
            for (int i = 2; i <= lastNz; i++) {
                printf ("%i ", convert(7,i,0));
            }
            // or else c7 *must* have a zero at forcedZero
            printf ("%i 0\n", convert(7,forcedZero,0));
        }
    }
    // c3 has more nonzeros than c11
    for (int lastNz = 3; lastNz+1 < N; lastNz++) {
        for (int forcedZero = lastNz+1; forcedZero < N; forcedZero++) {
            // if c3[lastNz] != 0 and c3[lastNz+1] = 0,
            printf ("%i -%i ", convert(3,lastNz,0), convert(3,lastNz+1,0));
            // then c11 must have a zero in cols 2..lastNz
            for (int i = 2; i <= lastNz; i++) {
                printf ("%i ", convert(11,i,0));
            }
            // or else c11 *must* have a zero at forcedZero
            printf ("%i 0\n", convert(11,forcedZero,0));
        }
    }

    // c3 has more nonzeros than c19
    for (int lastNz = 4; lastNz+1 < N; lastNz++) {
        for (int forcedZero = lastNz+1; forcedZero < N; forcedZero++) {
            // if c3[lastNz] != 0 and c3[lastNz+1] = 0,
            printf ("%i -%i ", convert(3,lastNz,0), convert(3,lastNz+1,0));
            // then c19 must have a zero in cols 2..lastNz
            for (int i = 2; i <= lastNz; i++) {
                printf ("%i ", convert(19,i,0));
            }
            // or else c19 *must* have a zero at forcedZero
            printf ("%i 0\n", convert(19,forcedZero,0));
        }
    }
}

int main (int argc, char** argv) {
  if (argc < 3) {
    printf ("Keller encode requires two arguments: N and S\n"); exit (0); }

  N = atoi (argv[1]);
  S = atoi (argv[2]);

  int nVars = (1 << (N-1)) * N * (N * S + S + (1 << (N-1)));
  int nCls  = (1 << N) * N * (1 + S * (S-1) / 2);
  nCls     += (1 << N) * N * (2*S*N - 2*S + 1) / 2;
  nCls     += (1 << (2*N - 1)) * N * S + (1 << N) * ((1 << N)-1) / 2;

  // number of SB clauses
  nCls += 2 * N + N-3;
  nCls += (N-2) * (N-3) / 2;
  nCls += (N-3) * (N-4) / 2;
  nCls += (N-4) * (N-5) / 2;

  printf ("p cnf %i %i\n", nVars, nCls);

  /* Assert that for all cubes w and coordinates i
     exactly one of x_{w,i,0}, ..., x_{w,i,S-1} is true */
  for (int w = 0; w < (1 << N); w++)
    for (int i = 0; i < N; i++) {
      /* at least one true */
      for (int c = 0; c < S; c++) printf ("%i ", convert(w, i, c));
      printf ("0\n");

      /* at most one true */
      for (int c = 0; c < S; c++)
        for (int cc = c+1; cc < S; cc++)
          printf ("-%i -%i 0\n", convert(w, i, c), convert(w, i, cc));
    }

  gen_edges();

  sym_break();
}