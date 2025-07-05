#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <stdbool.h>

#define SBP

/* N is the dimension, S is the number of different shifts (modulo 1) */
/* In the paper, N = 7 and S = {3,4,6} */
int N, S;

// use sequential counter exactly1 instead of pairwise AMO encoding
//#define SEQCOUNTER

// if defined, outputs extra symmetry breaking clauses
// that are normally verified by SR proof
#define EXTRA_SB

// if defined, outputs an increment CNF with appropriate cubes.
// the cube split is normally verified by SR proof.
#define CUBES


/* converts indicator for index w, coordinate i, shift c
to a CNF variable (x_{w,i,c} notation in paper) */
int var_x(int w, int i, int c) {
  assert(w >= 0 && w < (1 << N));
  assert(i >= 0 && i < N);
  assert(c >= 0 && c < S);
  return 1 + S*N*w + S*i + c;
}


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
  // the next available var
  int var = 1 + (1 << N) * N * S;
  #ifdef SEQCOUNTER
  var += (1 << N) * N * S;
  #endif

  // second difference clauses
  for (int w = 0; w < (1 << N); w++) {
    for (int iFlip = 0; iFlip < N; iFlip++) {
      int ww = w ^ (1 << iFlip);
      if (w < ww) {

        // y variables are var + i

        for (int i = 0; i < N; i++) {
          if (i != iFlip) {
            printf ("%i ", var + i);
          }
        }
        printf ("0\n");
      
        for (int i = 0; i < N; i++) {
          if (i != iFlip) {
            for (int c = 0; c < S; c++) {
              printf ("-%i -%i -%i 0\n", var + i, var_x(w, i, c), var_x (ww, i, c));
            }
          }
        }
  
        // used N variables for y
        var += N;
      }
    }
  }

  // s gap clauses
  for (int w = 0; w < (1 << N); w++) {
    for (int ww = w+1; ww < (1 << N); ww++) {
      int xor = w ^ ww;

      // z variables are var + i

      /* of the bits which w and ww differ in, they must be EXACTLY the same in one place */
      for (int i = 0; i < N; i++) {
        if (xor & (1 << i)) {
          printf ("%i ", var + i);
        }
      }
      printf ("0\n");

      for (int i = 0; i < N; i++) {
        if (xor & (1 << i)) {
          for (int c = 0; c < S; c++) {
            printf ("-%i %i -%i 0\n", var + i, var_x(w, i, c), var_x (ww, i, c));
            printf ("-%i -%i %i 0\n", var + i, var_x(w, i, c), var_x (ww, i, c));
          }
        }
      }

      // we used N variables for the z ones
      var += N;

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

void extra_sym_break() {
  if (N < 5 || S < 4) return;

  // c3[j] < 2 for j >= 2
  for (int j = 2; j < N; j++) {
    for (int k = 2; k < S; k++) {
      printf("-%i 0\n", var_x(3,j,k));
    }
  }

  // fix c3 at j=2,3,4; I include the clauses exactly as they are from the DSR proof.
  printf("%i 0\n", var_x(3,2,1));
  printf("%i 0\n", var_x(3,3,1));
  printf("-%i %i 0\n", var_x(7,3,1), var_x(3,4,1));
  printf("-%i %i 0\n", var_x(11,2,1), var_x(3,4,1));
  printf("%i 0\n", var_x(3,4,1));
}

void gen_cubes() {
  if (N < 5 || S < 4) return;

  int canon_mats[28][6] = {
    { 1, 0, 0, 1, 1, 0}, { 1, 1, 1, 2, 0, 1}, { 1, 1, 1, 1, 1, 0}, { 1, 1, 0, 0, 2, 1},
    { 1, 2, 0, 1, 1, 2}, { 1, 1, 1, 1, 1, 2}, { 1, 1, 0, 1, 2, 2}, { 1, 1, 2, 1, 2, 2},
    { 1, 0, 1, 0, 1, 1}, { 1, 1, 0, 1, 2, 0}, { 1, 1, 0, 2, 2, 1}, { 1, 2, 0, 2, 1, 1},
    { 1, 2, 1, 3, 1, 1}, { 1, 0, 0, 1, 1, 2}, { 1, 1, 2, 1, 3, 2}, { 1, 0, 1, 2, 1, 1},
    { 1, 1, 1, 1, 2, 2}, { 1, 1, 0, 1, 0, 2}, { 1, 1, 0, 1, 0, 0}, { 1, 2, 1, 2, 1, 1},
    { 1, 2, 2, 1, 1, 2}, { 1, 1, 1, 1, 0, 2}, { 1, 1, 1, 0, 2, 1}, { 1, 1, 1, 1, 1, 1},
    { 1, 1, 1, 0, 0, 1}, { 1, 1, 1, 1, 0, 0}, { 1, 2, 0, 3, 1, 1}, { 1, 1, 1, 2, 2, 1},
  };

  int canon_cols[52][4] = {
    {0, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, 1, 0}, {0, 0, 1, 1}, {0, 0, 1, 2},
    {0, 1, 0, 0}, {0, 1, 0, 1}, {0, 1, 0, 2}, {0, 1, 1, 0}, {0, 1, 1, 1},
    {0, 1, 1, 2}, {0, 1, 2, 0}, {0, 1, 2, 1}, {0, 1, 2, 2}, {0, 1, 2, 3},
    {1, 0, 0, 0}, {1, 0, 0, 1}, {1, 0, 0, 2}, {1, 0, 1, 0}, {1, 0, 1, 1},
    {1, 0, 1, 2}, {1, 0, 2, 0}, {1, 0, 2, 1}, {1, 0, 2, 2}, {1, 0, 2, 3},
    {1, 1, 0, 0}, {1, 1, 0, 1}, {1, 1, 0, 2}, {1, 1, 1, 0}, {1, 1, 1, 1},
    {1, 1, 1, 2}, {1, 1, 2, 0}, {1, 1, 2, 1}, {1, 1, 2, 2}, {1, 1, 2, 3},
    {1, 2, 0, 0}, {1, 2, 0, 1}, {1, 2, 0, 2}, {1, 2, 0, 3},
    {1, 2, 1, 0}, {1, 2, 1, 1}, {1, 2, 1, 2}, {1, 2, 1, 3},
    {1, 2, 2, 0}, {1, 2, 2, 1}, {1, 2, 2, 2}, {1, 2, 2, 3},
    {1, 2, 3, 0}, {1, 2, 3, 1}, {1, 2, 3, 2}, {1, 2, 3, 3}, {1, 2, 3, 4},
  };

  for (int midx = 0; midx < 28; midx++) {
    int *mat = canon_mats[midx];

    int cidx[N-5]; for (int c = 0; c < N-5; c++) cidx[c] = 0;
  
    bool running = true;
    while (running) {
      printf("a %i %i %i %i %i %i ", var_x(7,3,mat[0]), var_x(7,4,mat[1]),
        var_x(11,2,mat[2]), var_x(11,4,mat[3]), var_x(19,2,mat[4]), var_x(19,3,mat[5]));
      for (int j = 5; j < N; j++) {
        int *col = canon_cols[cidx[j-5]];
        printf("%i %i %i %i ", var_x(3,j,col[0]), var_x(7,j,col[1]), var_x(11,j,col[2]), var_x(19,j,col[3]));
      }
      printf("0\n");

      // step cidx
      running = false;
      for (int c = N-6; c >= 0; c--) {
        cidx[c] = (cidx[c]+1) % 52;
        if (cidx[c] > 0) {
          for (int c2 = c+1; c2 < N-5; c2++) {
            cidx[c2] = cidx[c];
          }
          running = true;
          break;
        }
      }
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
  // AMO clauses
  #ifdef SEQCOUNTER
    nCls += (1 << N) * N * (4 * S - 1);
  #else
    nCls += (1 << N) * N * (1 + S * (S-1) / 2);
  #endif
  // two diff clauses. counting:
  //   iter over N dims for the one flipped bit
  //     iter over 2^(N-1) assignments to the other bits
  //       1 + (N-1)*S clauses in each iter
  nCls += N * (1 << (N-1)) * (1 + (N-1) * S);
  // s gap clauses. counting:
  //   iter over (2^N choose 2) pairs
  //     1 clause (the long clause) for each iter
  //   iter over j in N dims
  //     iter over 2^(2N-2) pairs of indices s.t. different at j and first < second
  //       2*S clauses
  nCls += (1 << N) * ((1 << N)-1) / 2 + N * (1 << (2*N - 1)) * S;

  // number of SB clauses
  nCls += 2 * N + N-3;
  if (N >= 5) {
    nCls += (N-2) * (N-3) / 2;
    nCls += (N-3) * (N-4) / 2;
    nCls += (N-4) * (N-5) / 2;
  }

  #ifdef EXTRA_SB
  if (N >= 5 && S >= 4) {
    nCls += (N-2) * (S-2) + 5;
  }
  #endif


  #ifdef CUBES
  printf("p inccnf\n");
  #else
  printf ("p cnf %i %i\n", nVars, nCls);
  #endif

  gen_coords();

  gen_edges();

  sym_break();

  #ifdef EXTRA_SB
  extra_sym_break();
  #endif

  #ifdef CUBES
  gen_cubes();
  #endif
}