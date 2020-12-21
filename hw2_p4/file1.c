#include <stdio.h>
#include <stdlib.h>

int puts(const char *s) {
    return 0;
}

int main(int argc, char **argv) {
    puts(argv[2]);
    return 0;
}

