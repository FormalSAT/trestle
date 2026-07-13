#include <ctype.h>
#include <stdio.h>
#include <lean/lean.h>

bool uint8_is_digit(uint8_t ch) {
  return isdigit(ch);
}

bool uint8_is_space(uint8_t ch) {
  return isspace(ch);
}

bool uint32_is_digit(uint32_t ch) {
  return isdigit(ch);
}

bool uint32_is_space(uint32_t ch) {
  return isspace(ch);
}
