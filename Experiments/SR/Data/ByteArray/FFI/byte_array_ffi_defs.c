#include <ctype.h>
#include <stdio.h>
#include <lean/lean.h>

size_t lean_byte_array_ws(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  for (; iter < arr_size; iter++) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (!isspace(ch)) {
      break;
    }
  }

  return iter; 
}

size_t lean_byte_array_line(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  for (; iter < arr_size; iter++) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (ch == '\n') {
      return iter + 1;
    }
  }

  return iter;
}

size_t lean_byte_array_token(lean_object*arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  for (; iter < arr_size; iter++) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (!isspace(ch)) {
      break;
    }
  }

  for (; iter < arr_size; iter++) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (isspace(ch)) {
      break;
    }
  }

  return iter;
}

size_t lean_byte_array_skip_nat_no_ws(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  for (; iter < arr_size; iter++) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (!isdigit(ch)) {
      break; 
    }
  }

  return iter; 
}

size_t lean_byte_array_skip_int_no_ws(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  if (iter < arr_size) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (ch == '-') {
      iter++;
    }
  }

  return lean_byte_array_skip_nat_no_ws(arr, iter);
}

////////////////////////////////////////////////////////////////////////////////
// readNat, readInt
////////////////////////////////////////////////////////////////////////////////

static lean_obj_res lean_byte_array_read_panic_oob(lean_obj_arg def_val) {
  return lean_panic_fn(def_val, lean_mk_ascii_string_unchecked(
    "Attempted to read a number, but the iterator is out of bounds."));
}

static lean_obj_res lean_byte_array_read_panic_nan(lean_obj_arg def_val) {
  return lean_panic_fn(def_val, lean_mk_ascii_string_unchecked(
    "Attempted to read a number, but the first non-whitespace character is not a digit or '-': "));
}

uint32_t lean_byte_array_read_uint32_no_ws(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  if (iter < arr_size) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (!isdigit(ch)) {
      lean_byte_array_read_panic_nan(lean_box_uint32((uint32_t) ch));
    }

    uint32_t acc = 0;
    for (; iter < arr_size; iter++) {
      ch = lean_byte_array_uget(arr, iter);
      if (!isdigit(ch)) {
        break;
      }

      acc = acc * 10 + ((uint32_t) (ch - '0'));
    }

    return acc;
  } else {
    lean_byte_array_read_panic_oob(lean_box_usize(iter));
    return 0; // Unreachable
  }
}

lean_object* lean_byte_array_read_int32_no_ws(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  if (iter < arr_size) {
    uint8_t ch = lean_byte_array_uget(arr, iter);

    // Handle a starting minus sign
    int starts_with_minus = 0;
    if (ch == '-') {
      iter++;
      starts_with_minus = 1;
    }
    
    int32_t acc = (int32_t) lean_byte_array_read_uint32_no_ws(arr, iter);

    if (starts_with_minus) {
      acc = -acc;
    }

    return lean_int32_to_int((uint32_t) acc);
  } else {
    lean_byte_array_read_panic_oob(lean_box_usize(iter));
    return NULL; // Unreachable
  }
}

uint64_t lean_byte_array_read_uint64_no_ws(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  if (iter < arr_size) {
    uint8_t ch = lean_byte_array_uget(arr, iter);
    if (!isdigit(ch)) {
      lean_byte_array_read_panic_nan(lean_box_uint32((uint32_t) ch));
    }

    uint64_t acc = 0;
    for (; iter < arr_size; iter++) {
      ch = lean_byte_array_uget(arr, iter);
      if (!isdigit(ch)) {
        break;
      }

      acc = acc * 10 + ((uint64_t) (ch - '0'));
    }

    return acc;
  } else {
    lean_byte_array_read_panic_oob(lean_box_usize(iter));
    return 0; // Unreachable
  }
}

lean_object* lean_byte_array_read_int64_no_ws(lean_object* arr, size_t iter) {
  size_t arr_size = lean_sarray_size(arr);
  if (iter < arr_size) {
    uint8_t ch = lean_byte_array_uget(arr, iter);

    // Handle a starting minus sign
    int starts_with_minus = 0;
    if (ch == '-') {
      iter++;
      starts_with_minus = 1;
    }
    
    int64_t acc = (int64_t) lean_byte_array_read_uint64_no_ws(arr, iter);

    if (starts_with_minus) {
      acc = -acc;
    }

    return lean_int64_to_int((uint64_t) acc);
  } else {
    lean_byte_array_read_panic_oob(lean_box_usize(iter));
    return NULL; // Unreachable
  }
}
