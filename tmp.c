#include <stdio.h>

int main() {
  int x = 10;
  int y = 2;
  int i = 0;
  int j = 0;
  long a = 1;
  int b = 0;

  while ( i < x ) {
    j = 0;
    b = a;
    a = 0;

    while ( j < y ) {
      a = a + b;
      j = j + 1;
    }

    i = i + 1;
  }

  printf("x: %d, y: %d\n", x, y);
  printf("y^x: %ld\n", a);

  return 0;
}
