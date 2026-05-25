
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

void ntt(uint16_t *A); /* Ours */
void fft(uint16_t *A); /* Masuda's */

#define Q ((uint16_t)12289)

int main(int argc, char **argv) {
  srand(time(NULL));
  uint16_t A[1024] = {};
  uint16_t B[1024] = {};
  for (size_t i = 0; i < 1024; ++i) {
    uint16_t r = (uint16_t)rand() % Q;
    A[i] = r; B[i] = r;
  }
  ntt(A);
  fft(B);

  for (size_t i = 0; i < 1024; ++i) {
    uint16_t a = A[i] % Q;
    uint16_t b = A[i] % Q;
    printf("[%04zu] %5" PRIu16 "; %5" PRIu16 "%s\n", i, a, b,
           a == b ? "" : " X");
    if (a != b) return 1;
  }
}
