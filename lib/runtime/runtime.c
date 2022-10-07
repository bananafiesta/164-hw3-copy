#include <stdio.h>
#include <inttypes.h>

extern uint64_t lisp_entry();

#define num_mask   0b11
#define num_tag    0b00
#define num_shift  2

#define bool_mask  0b1111111
#define bool_tag   0b0011111
#define bool_shift 7

void print_value(uint64_t value) {
  if ((value & num_mask) == num_tag) {
    int64_t ivalue = (int64_t)value;
    printf("%" PRIi64, ivalue >> num_shift);
  } else if ((value & bool_mask) == bool_tag) {
    if (value >> bool_shift) {
      printf("true");
    }
    else {
      printf("false");
    }
  } else {
    printf("BAD VALUE: %" PRIu64, value);
  }
}

int main(int argc, char **argv) {
  print_value(lisp_entry());
  return 0;
}
