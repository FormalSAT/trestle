#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#define SBP

/* N is the dimension, S is the number of different shifts (modulo 1) */
/* In the paper, N = 7 and S = {3,4,6} */
int N, S;

/* converts indicator for index w, coordinate i, shift c
to a CNF variable (x_{w,i,c} notation in paper) */
int var_x(int w, int i, int c) {
  assert(w >= 0 && w < (1 << N));
  assert(i >= 0 && i < N);
  assert(c >= 0 && c < S);
  return S*N*w + S*i + c + 1;
}

// if defined, uses sequential counter instead of pairwise AMO encoding
#define SEQCOUNTER

/* Assert that for all cubes w and coordinates i
   exactly one of x_{w,i,0}, ..., x_{w,i,S-1} is true */
void gen_coords() {
  #ifdef SEQCOUNTER
  // the last var used so far
  int var = (1 << N) * N * S;

  for (int w = 0; w < (1 << N); w++) {
    for (int i = 0; i < N; i++) {
      // for every k we need:
      //    s(k) => s(k-1) \/ x(k)
      //    s(k) <= s(k-1)
      //    s(k) <= x(k)
      //    not s(k-1) \/ not x(k)

      // for k = 0, treat s(k-1) like false
      printf("-%i %i 0\n", var + var_x(w,i,0), var_x(w,i,0));
      printf("%i -%i 0\n", var + var_x(w,i,0), var_x(w,i,0));

      for (int k = 1; k < S; k++) {
        int x = var_x(w,i,k);
        int s_pred = var + var_x(w,i,k-1);
        int s = var + var_x(w,i,k);
        printf("-%i %i %i 0\n", s, s_pred, x);
        printf("%i -%i 0\n",    s, s_pred);
        printf("%i -%i 0\n",    s,         x);
        printf("-%i -%i 0\n", s_pred, x);
      }

      // and the last s var must be true, to force at least one
      printf("%i 0\n", var + var_x(w,i,S-1));
    }
  }

  #else

  // Pairwise encoding
  for (int w = 0; w < (1 << N); w++)
    for (int i = 0; i < N; i++) {
      /* at least one true */
      for (int c = 0; c < S; c++) printf ("%i ", var_x(w, i, c));
      printf ("0\n");

      /* at most one true */
      for (int c = 0; c < S; c++)
        for (int cc = c+1; cc < S; cc++)
          printf ("-%i -%i 0\n", var_x(w, i, c), var_x(w, i, cc));
    }
  #endif
}

/* Assert for every pair of cubes w, ww that they do not intersect
   and do not faceshare */
void gen_edges() {
  // the last var used so far
  int var = (1 << N) * N * S;
  #ifdef SEQCOUNTER
  var += (1 << N) * N * S;
  #endif

  for (int w = 0; w < (1 << N); w++) {
    for (int ww = w+1; ww < (1 << N); ww++) {
      int j = 0;
      int xor = w ^ ww;

      // z variables are var + j

      /* of the bits which w and ww differ in, they must be EXACTLY the same in one place */
      for (int i = 0; i < N; i++) {
        if (xor & (1 << i)) {
          j++;
          printf ("%i ", var + j);
        }
      }
      printf ("0\n");

      j = 0;

      for (int i = 0; i < N; i++) {
        if (xor & (1 << i)) {
          j++;
          for (int c = 0; c < S; c++) {
            printf ("-%i %i -%i 0\n", var + j, var_x(w, i, c), var_x (ww, i, c));
            printf ("-%i -%i %i 0\n", var + j, var_x(w, i, c), var_x (ww, i, c));
          }
        }
      }

      // # of z variables was j
      var += j;

      /* do w and ww differ only in one coordinate ? */
      if (__builtin_popcount(xor) == 1) {

        // y variables are var + j
        j = 0;
        for (int i = 0; i < N; i++) {
          if (xor != (1 << i))
            for (int c = 0; c < S; c++) {
              j++;
              printf ("%i ", var + j);
            }
        }
        printf ("0\n");
      
        j = 0;
        for (int i = 0; i < N; i++) {
          if (xor != (1 << i)) {
            for (int c = 0; c < S; c++) {
              j++;
              printf ("-%i  %i  %i 0\n", var + j, var_x(w, i, c), var_x (ww, i, c));
              printf ("-%i -%i -%i 0\n", var + j, var_x(w, i, c), var_x (ww, i, c));
            }
          }
        }
  
        // # of y variables was j
        var += j;
      }
    }
  }
}

void sym_break() {
    // set c0
    for (int i = 0; i < N; i++) {
        printf ("%i 0\n", var_x(0, i, 0));
    }
    // set c1
    printf ("%i 0\n", var_x(1, 0, 0));
    printf ("%i 0\n", var_x(1, 1, 1));
    for (int i = 2; i < N; i++) {
        printf ("%i 0\n", var_x(1, i, 0));
    }
    
    // c3 sort zeros to the right
    for (int i = 2; i+1 < N; i++) {
        printf ("-%i %i 0\n", var_x(3, i, 0), var_x(3, i+1, 0));
    }

    if (N < 5) return;

    // c3 has more nonzeros than c7
    for (int lastNz = 2; lastNz+1 < N; lastNz++) {
        for (int forcedZero = lastNz+1; forcedZero < N; forcedZero++) {
            // if c3[lastNz] != 0 and c3[lastNz+1] = 0,
            printf ("%i -%i ", var_x(3,lastNz,0), var_x(3,lastNz+1,0));
            // then c7 must have a zero in cols 2..lastNz
            for (int i = 2; i <= lastNz; i++) {
                printf ("%i ", var_x(7,i,0));
            }
            // or else c7 *must* have a zero at forcedZero
            printf ("%i 0\n", var_x(7,forcedZero,0));
        }
    }
    // c3 has more nonzeros than c11
    for (int lastNz = 3; lastNz+1 < N; lastNz++) {
        for (int forcedZero = lastNz+1; forcedZero < N; forcedZero++) {
            // if c3[lastNz] != 0 and c3[lastNz+1] = 0,
            printf ("%i -%i ", var_x(3,lastNz,0), var_x(3,lastNz+1,0));
            // then c11 must have a zero in cols 2..lastNz
            for (int i = 2; i <= lastNz; i++) {
                printf ("%i ", var_x(11,i,0));
            }
            // or else c11 *must* have a zero at forcedZero
            printf ("%i 0\n", var_x(11,forcedZero,0));
        }
    }

    // c3 has more nonzeros than c19
    for (int lastNz = 4; lastNz+1 < N; lastNz++) {
        for (int forcedZero = lastNz+1; forcedZero < N; forcedZero++) {
            // if c3[lastNz] != 0 and c3[lastNz+1] = 0,
            printf ("%i -%i ", var_x(3,lastNz,0), var_x(3,lastNz+1,0));
            // then c19 must have a zero in cols 2..lastNz
            for (int i = 2; i <= lastNz; i++) {
                printf ("%i ", var_x(19,i,0));
            }
            // or else c19 *must* have a zero at forcedZero
            printf ("%i 0\n", var_x(19,forcedZero,0));
        }
    }
}

int main (int argc, char** argv) {
  if (argc < 3) {
    printf ("Keller encode requires two arguments: N and S\n"); exit (0); }

  N = atoi (argv[1]);
  S = atoi (argv[2]);

  assert(N > 1);
  assert(S > 1);

  int nVars = (1 << (N-1)) * N * (N * S + S + (1 << (N-1)));

  #ifdef SEQCOUNTER
  nVars += (1 << N) * N * S;
  #endif

  int nCls  = 0;
  #ifdef SEQCOUNTER
    nCls += (1 << N) * N * (4 * S - 1);
  #else
    nCls += (1 << N) * N * (1 + S * (S-1) / 2);
  #endif
  nCls += (1 << N) * N * (2*S*N - 2*S + 1) / 2;
  nCls += (1 << (2*N - 1)) * N * S + (1 << N) * ((1 << N)-1) / 2;

  // number of SB clauses
  nCls += 2 * N + N-3;
  if (N >= 5) {
    nCls += (N-2) * (N-3) / 2;
    nCls += (N-3) * (N-4) / 2;
    nCls += (N-4) * (N-5) / 2;
  }

  printf ("p cnf %i %i\n", nVars, nCls);

  gen_coords();

  gen_edges();

  sym_break();
}